module Veritas.Intermediate.VerifySKC
open Veritas.Intermediate.Logs
open Veritas.Intermediate.Store

module BT = Veritas.BinTree
module FE = FStar.FunctionalExtensionality
module H = Veritas.Hash
module K = Veritas.Key
module MH = Veritas.MultiSetHash
module MHD = Veritas.MultiSetHashDomain
module R = Veritas.Record
module SA = Veritas.SeqAux
module V = Veritas.Verifier
module VT = Veritas.Verifier.Thread

let data_key = K.data_key
let merkle_key = K.merkle_key
let data_value = R.data_value 
let thread_id = V.thread_id
let timestamp = MHD.timestamp

(* Thread-local state
   id     : thread id
   st     : thread local store
   clock  : current timestamp
   hadd   : add set hash
   hevict : evict set hash *)
noeq
type vtls =
  | Failed : vtls
  | Valid :
    id : thread_id ->
    st : vstore ->
    clock : timestamp ->
    hadd : MH.ms_hash_value ->
    hevict : MH.ms_hash_value ->
    vtls

let thread_id_of (vs:vtls {Valid? vs}): thread_id = 
  Valid?.id vs

let thread_store (vs: vtls {Valid? vs}): vstore =
  Valid?.st vs

let thread_store_is_map (vs: vtls {Valid? vs}): bool =
  let st = thread_store vs in st.is_map

let update_thread_store (vs:vtls {Valid? vs}) (st:vstore) : vtls =
  match vs with
  | Valid id _ clock hadd hevict -> Valid id st clock hadd hevict

let thread_clock (vs:vtls {Valid? vs}) = 
  Valid?.clock vs

let update_thread_clock (vs:vtls {Valid? vs}) (clock:timestamp): vtls = 
  match vs with
  | Valid id st _ hadd hevict -> Valid id st clock hadd hevict

let thread_hadd (vs:vtls {Valid? vs}) = 
  Valid?.hadd vs

let thread_hevict (vs:vtls {Valid? vs}) = 
  Valid?.hevict vs

let update_thread_hadd (vs:vtls {Valid? vs}) (hadd: MH.ms_hash_value): vtls = 
  match vs with
  | Valid id st clock _ hevict -> Valid id st clock hadd hevict

let update_thread_hevict (vs:vtls {Valid? vs}) (hevict:MH.ms_hash_value): vtls = 
  match vs with
  | Valid id st clock hadd _ -> Valid id st clock hadd hevict

let vget (s:slot_id) (k:data_key) (v:data_value) (vs: vtls {Valid? vs}) : vtls =
  let st = thread_store vs in
  (* check store contains slot s *)
  if not (contains_record st s) then Failed
  (* check stored key and value *)
  else let k' = get_key_at st s in
       let v' = get_value_at st s in
       if k' <> k then Failed
       else if not (R.DVal? v') then Failed
       else if R.to_data_value v' <> v then Failed
       else vs

let vput (s:slot_id) (k:data_key) (v:data_value) (vs: vtls {Valid? vs}) : vtls =
  let st = thread_store vs in
  (* check store contains slot s *)
  if not (contains_record st s) then Failed
  (* check stored key is k *)
  else if get_key_at st s <> k then Failed
  else update_thread_store vs (update_record_value st s (R.DVal v))

let vaddm (s:slot_id) (r:R.record) (s':slot_id) (k0':merkle_key) (vs: vtls {Valid? vs}): vtls =
  let st = thread_store vs in
  if not (s < Seq.length st.data) then Failed
  (* check store contains slot s' *)
  else if not (contains_record st s') then Failed
  else
    let (k,v) = r in
    let k' = get_key_at st s' in
    let v' = get_value_at st s' in
    let a' = get_add_method_at st s' in 
    (* check key is consistent with argument *)
    if k' <> k0' then Failed
    (* check k is a proper desc of k' *)
    else if not (BT.is_proper_desc k k') then Failed
    (* check store does not contain slot s *)
    else if contains_record st s then Failed
    (* check type of v is consistent with k *)
    else if not (R.is_value_of k v) then Failed
    (* check v' is a merkle value *)
    else if R.DVal? v' then Failed 
    else
      let v' = R.to_merkle_value v' in
      let d = BT.desc_dir k k' in
      let dh' = R.desc_hash_dir v' d in 
      (* check k is not already in the store
         >> in lower levels we will check this via 'in_store' fields in records *)
      if contains_key st k then Failed
      else let h = H.hashfn v in
      match dh' with
      | R.Empty -> (* k' has no child in direction d *)
                (* first add --> init value *)
                if v <> R.init_value k then Failed
                else
                  let v'_upd = V.update_merkle_value v' d k h false in
                  let st_upd = update_record_value st s' (R.MVal v'_upd) in
                  let st_upd2 = add_record st_upd s k v V.MAdd in
                  update_thread_store vs st_upd2
      | R.Desc k2 h2 b2 -> if k2 = k then
                          (* k is a child of k' *)
                          (* check hashes match and k was not evicted to blum *)
                          if not (h2 = h && b2 = false) then Failed
                          else update_thread_store vs (add_record st s k v V.MAdd)
                          (* k is not a child of k' *)
                          (* first add --> init value *)
                        else if v <> R.init_value k then Failed
                        (* check k2 is a proper desc of k *)
                        else if not (BT.is_proper_desc k2 k) then Failed
                        else
                          let d2 = BT.desc_dir k2 k in
                          let mv = R.to_merkle_value v in
                          let mv_upd = V.update_merkle_value mv d2 k2 h2 b2 in
                          let v'_upd = V.update_merkle_value v' d k h false in
                          let st_upd = update_record_value st s' (R.MVal  v'_upd) in
                          let st_upd2 = add_record st_upd s k (R.MVal mv_upd) V.MAdd in
                          update_thread_store vs st_upd2

(* key k is in store and was added using Merkle *)
let is_instore_madd (st: vstore) (k: key): bool = 
  contains_key st k && 
  add_method_of st k = V.MAdd

let has_instore_merkle_desc (st:vstore) (k:key{contains_key st k}): bool = 
  if K.is_data_key k then false
  else 
    let v = R.to_merkle_value (value_of st k) in
    let ld = R.desc_hash_dir v BT.Left in
    let rd = R.desc_hash_dir v BT.Right in
    R.Desc? ld && is_instore_madd st (R.Desc?.k ld) || 
    R.Desc? rd && is_instore_madd st (R.Desc?.k rd)

let vevictm (s:slot_id) (k0:key) (s':slot_id) (k0':merkle_key) (vs: vtls {Valid? vs}): vtls = 
  let st = thread_store vs in
  (* check store contains s and s' *)
  if not (contains_record st s && contains_record st s') then Failed
  else 
    let k = get_key_at st s in
    let v = get_value_at st s in
    let a = get_add_method_at st s in
    let k' = get_key_at st s' in
    let v' = get_value_at st s' in
    let a' = get_add_method_at st s' in
    (* check keys are consistent with arguments *)
    if k <> k0 then Failed
    else if k' <> k0' then Failed
    (* check k is a proper descendent of k' *)
    else if not (BT.is_proper_desc k k') then Failed
    (* check k does not have a child in the store *)
    else if (
              lemma_contains_key st s k; 
              has_instore_merkle_desc st k
            ) then Failed
    else 
      let d = BT.desc_dir k k' in
      let v' = R.to_merkle_value v' in
      let dh' = R.desc_hash_dir v' d in
      let h = H.hashfn v in
      match dh' with
      | R.Empty -> Failed
      | R.Desc k2 h2 b2 -> if k2 <> k then Failed
                        else
                          let v'_upd = V.update_merkle_value v' d k h false in
                          let st_upd = evict_record (update_record_value st s' (R.MVal v'_upd)) s in
                         update_thread_store vs st_upd

let vaddb (s:slot_id) (r:R.record) (t:timestamp) (j:thread_id) (vs:vtls {Valid? vs}): vtls = 
  let st = thread_store vs in 
  if not (s < Seq.length st.data) then Failed
  (* epoch of timestamp of last evict *)
  else 
    let e = MHD.MkTimestamp?.e t in
    let (k,v) = r in
    (* check value type consistent with key k *)
    if not (R.is_value_of k v) then Failed
    (* check store contains slot s *)
    else if contains_record st s then Failed
    else 
      (* update add hash *)
      let h = thread_hadd vs in
      let h_upd = MH.ms_hashfn_upd (MHD.MHDom (k,v) t j) h in
      let vs_upd = update_thread_hadd vs h_upd in
      (* update clock *)
      let clk = thread_clock vs in
      let clk_upd = V.max clk (MHD.next t) in
      let vs_upd2 = update_thread_clock vs_upd clk_upd in
      (* check k is not in the store; update the valid flag accordingly *)
      let valid = not (contains_key st k) in
      let st_upd = update_is_map st (st.is_map && valid) in
      (* add record to store *)
      let st_upd2 = add_record st_upd s k v V.BAdd in
      update_thread_store vs_upd2 st_upd2

let vevictb (s:slot_id) (k0:key) (t:timestamp) (vs:vtls {Valid? vs}): vtls = 
  let clock = thread_clock vs in
  let e = MHD.MkTimestamp?.e t in
  let st = thread_store vs in
  (* check store contains slot s *)
  if not (contains_record st s) then Failed
  else
    let k = get_key_at st s in
    let v = get_value_at st s in
    (* check key is consistent with argument *)
    if k <> k0 then Failed
    (* check key at s is not root *)
    else if k = BT.Root then Failed
    (* check time of evict < current time *)
    else if not (MHD.ts_lt clock t) then Failed
    (* check s was added through blum *)  
    else if get_add_method_at st s <> V.BAdd then Failed
    (* check k has no children n the store *)
    else if (
              lemma_contains_key st s k;
              has_instore_merkle_desc st k
            ) then Failed  
    else 
      (* update evict hash *)
      let h = thread_hevict vs in
      let h_upd = MH.ms_hashfn_upd (MHD.MHDom (k,v) t (thread_id_of vs)) h in
      let vs_upd = update_thread_hevict vs h_upd in
      (* update clock *)
      let vs_upd2 = update_thread_clock vs_upd t in    
      (* evict record *)
      let st_upd = evict_record st s in
      update_thread_store vs_upd2 st_upd

let vevictbm (s:slot_id) (k0:key) (s':slot_id) (k0':merkle_key) (t:timestamp) (vs:vtls {Valid? vs}): vtls = 
  let st = thread_store vs in
  (* check store contains s and s' *)
  if not (contains_record st s && contains_record st s') then Failed
  else
    let k = get_key_at st s in
    let k' = get_key_at st s' in
    let v' = get_value_at st s' in
    (* check keys are consistent with arguments *)
    if k <> k0 then Failed
    else if k' <> k0' then Failed
    (* check k is a proper desc of k' *)
    else if not (BT.is_proper_desc k k') then Failed
    (* check s was added through merkle *)
    else if get_add_method_at st s <> V.MAdd then Failed  
    (* check k has no children in the store *)
    else if (
              lemma_contains_key st s k;
              has_instore_merkle_desc st k 
            ) then Failed  
    else
      let v' = R.to_merkle_value v' in
      let d = BT.desc_dir k k' in
      let dh' = R.desc_hash_dir v' d in
      match dh' with
      | R.Empty -> Failed
      | R.Desc k2 h2 b2 -> if k2 <> k || b2 then Failed
                          else
                            let v'_upd = V.update_merkle_value v' d k h2 true in
                            let st_upd = update_record_value st s' (R.MVal v'_upd) in
                            vevictb s k0 t (update_thread_store vs st_upd)

(* thread-level verification step
   (following the defn in Veritas.Verifier) *)
let t_verify_step (vs:vtls)
                  (e:logSK_entry): vtls =                           
  match vs with
  | Failed -> Failed (* could check the is_map flag here *)
  | _ ->
    match e with
    | Get_SK s k v -> vget s k v vs
    | Put_SK s k v -> vput s k v vs
    | AddM_SK s r s' k'  -> vaddm s r s' k' vs
    | EvictM_SK s k s' k' -> vevictm s k s' k' vs
    | AddB_SK s r t j -> vaddb s r t j vs
    | EvictB_SK s k t -> vevictb s k t vs
    | EvictBM_SK s k s' k' t -> vevictbm s k s' k' t vs

(* verify a log from a specified initial state *)
let rec t_verify_aux (vs:vtls) (l:logSK): Tot vtls
  (decreases (Seq.length l)) =
  let n = Seq.length l in
  if n = 0 then vs
  else
    let l' = SA.prefix l (n - 1) in
    let vs' = t_verify_aux vs l' in
    let e' = Seq.index l (n - 1) in
    t_verify_step vs' e'

// TODO: what should the initial size be?
let empty_store:vstore = { data=Seq.create 10 None; is_map=true }

(* initialize verifier state *)
let init_thread_state (id:thread_id): vtls = 
  let vs = Valid id empty_store (MHD.MkTimestamp 0 0) MHD.empty_hash_value MHD.empty_hash_value in  
  if id = 0 then
    let st0 = thread_store vs in
    let st0_upd = add_record st0 0 BT.Root (R.init_value BT.Root) V.MAdd in
    update_thread_store vs st0_upd    
  else vs

let t_verify (id:thread_id) (l:logSK): vtls = 
  t_verify_aux (init_thread_state id) l 

let verify (id:thread_id) (l:logSK): vtls =
  let vs = t_verify id l in
  if Valid? vs
  then if thread_store_is_map vs then vs else Failed
  else Failed

let verifiable (id:thread_id) (l: logSK): bool =
  Valid? (verify id l)

(** Proofs **)

module Spec = Veritas.Verifier

(* Relation between stores *)
let store_rel (st:vstore) (st':Spec.vstore) : Type = 
  st.is_map /\ FE.feq st' (as_map st)

(* Relation between thread-local states *)
let vtls_rel (vs:vtls) (vs':Spec.vtls) : Type =
  match vs, vs' with
  // either both runs failed
  | Failed, Spec.Failed -> True
  // or both are valid and the stores are related
  | Valid id st clk ha he, Spec.Valid id' st' clk' _ ha' he' ->
       store_rel st st' /\ 
       // other fields related by equality  
       id = id' /\ clk = clk' /\ ha = ha' /\ he = he'   
  // or the spec run failed, but the store of vs is not a map
  | Valid _ st _ _ _, _ -> not st.is_map
  | _, _ -> False

(* Relation between a slot and key *)
let is_key_of (vs: vtls {Valid? vs}) (s:slot_id) (k:key) =
  let st = thread_store vs in slot_key_equiv st s k

let lemma_contains_record_store_contains 
      (st:vstore) 
      (s:slot_id) 
      (st':Spec.vstore{store_rel st st'}) 
      (k:key{slot_key_equiv st s k})
  : Lemma (contains_record st s = Spec.store_contains st' k)
  = admit()

let lemma_get_value_at_stored_value
      (st:vstore) 
      (s:slot_id) 
      (st':Spec.vstore{store_rel st st'}) 
      (k:data_key{slot_key_equiv st s k /\ Spec.store_contains st' k})
  : Lemma (get_value_at st s = Spec.stored_value st' k)
  = admit()

let lemma_update_record_value_update_store
      (st:vstore) 
      (s:slot_id) 
      (st':Spec.vstore{store_rel st st'}) 
      (k:data_key{slot_key_equiv st s k /\ Spec.store_contains st' k})
      (v:data_value)
  : Lemma (store_rel (update_record_value st s (R.DVal v)) (Spec.update_store st' k (R.DVal v)))
  = admit()

let lemma_vget_simulates_spec 
      (vs:vtls{Valid? vs})
      (vs':Spec.vtls{Spec.Valid? vs'})
      (s:slot_id)
      (k:data_key)
      (v:data_value)
  : Lemma (requires (vtls_rel vs vs' /\ is_key_of vs s k))
          (ensures (vtls_rel (vget s k v vs) (Spec.vget k v vs')))
  = let st = thread_store vs in
    let st' = Spec.thread_store vs' in
    lemma_contains_record_store_contains st s st' k;
    lemma_get_value_at_stored_value st s st' k

let lemma_vput_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s:slot_id) 
      (k:data_key) 
      (v:data_value) 
  : Lemma (requires (vtls_rel vs vs' /\ is_key_of vs s k))
          (ensures (vtls_rel (vput s k v vs) (Spec.vput k v vs'))) 
  = let st = thread_store vs in
    let st' = Spec.thread_store vs' in
    lemma_contains_record_store_contains st s st' k;
    lemma_update_record_value_update_store st s st' k v

let lemma_vaddm_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s s':slot_id)
      (r:R.record)
      (k':merkle_key)  
  : Lemma (requires (vtls_rel vs vs'))
          (ensures (vtls_rel (vaddm s r s' k' vs) (Spec.vaddm r k' vs'))) 
  = admit()

let lemma_vevictm_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s s':slot_id)
      (k:key)
      (k':merkle_key)  
  : Lemma (requires (vtls_rel vs vs'))
          (ensures (vtls_rel (vevictm s k s' k' vs) (Spec.vevictm k k' vs'))) 
  = admit()

let lemma_vaddb_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s:slot_id)
      (r:R.record)
      (t:timestamp)
      (j:thread_id)
  : Lemma (requires (vtls_rel vs vs'))
          (ensures (vtls_rel (vaddb s r t j vs) (Spec.vaddb r t j vs'))) 
  = admit()

let lemma_vevictb_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s:slot_id)
      (k:key)
      (t:timestamp)
  : Lemma (requires (vtls_rel vs vs'))
          (ensures (vtls_rel (vevictb s k t vs) (Spec.vevictb k t vs'))) 
  = admit()

let lemma_vevictbm_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s s':slot_id)
      (k:key)
      (k':merkle_key)
      (t:timestamp)
  : Lemma (requires (vtls_rel vs vs'))
          (ensures (vtls_rel (vevictbm s k s' k' t vs) (Spec.vevictbm k k' t vs'))) 
  = admit()

(* Relation between logs *)
let log_rel  (l:logSK) (l':logK) : Type 
  = skc l /\ drop_slots l = l'

(* given a log with only slots, add consistent keys *)

(* given a log with keys and slots, check that the key accesses are consistent with evicts and adds *)

let lemma_t_verify_simulates_spec (id:thread_id) (l:logSK) (l':logK)
  : Lemma (requires (log_rel l l'))
          (ensures (vtls_rel (t_verify id l) (Spec.t_verify id l')))
  = admit()

(* For any log, the intermediate implementation will verify 
   iff the the spec implementation does. *)

let lemma_verifiable_simulates_spec (id:thread_id) (l:logSK) (l':logK)
  : Lemma (requires (log_rel l l'))
          (ensures (let tl : VT.thread_id_vlog = (id,l') in
                    verifiable id l = VT.verifiable tl))
  = lemma_t_verify_simulates_spec id l l';
    let vs = t_verify id l in
    if Valid? vs
    then if not (thread_store_is_map vs) 
    then admit()
