module Veritas.Intermediate.Verifier
open Veritas.Intermediate.Common
open Veritas.Intermediate.Store

module R = Veritas.Record
module K = Veritas.Key
module H = Veritas.Hash
module MH = Veritas.MultiSetHash
module MHD = Veritas.MultiSetHashDomain
module BT = Veritas.BinTree
module V = Veritas.Verifier
module SA = Veritas.SeqAux

(* id     : thread id
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

let vget (s:slot_id) (v:data_value) (vs: vtls {Valid? vs}): vtls =
  let st = thread_store vs in
  (* check store contains slot s *)
  if not (contains_record st s) then Failed
  (* check stored value is v *)
  else let v' = get_value_at st s in
       if not (R.DVal? v') then Failed
       else if R.to_data_value v' <> v then Failed
       else vs

let vput (s:slot_id) (v:data_value) (vs: vtls {Valid? vs}): vtls =
  let st = thread_store vs in
  (* check store contains slot s *)
  if not (contains_record st s) then Failed
  (* check stored key is a data key *)
  else if not (K.is_data_key (get_key_at st s)) then Failed
  else update_thread_store vs (update_record_value st s (R.DVal v))

let vaddm (s:slot_id) (r:record) (s':slot_id) (vs: vtls {Valid? vs}): vtls =
  let st = thread_store vs in
  if not (s < Seq.length st.data) then Failed
  (* check store contains slot s' *)
  else if not (contains_record st s') then Failed
  else
    let k = Record?.k r in
    let v = Record?.v r in
    let k' = get_key_at st s' in
    let v' = get_value_at st s' in
    let a' = get_add_method_at st s' in 
    (* check k is a proper desc of k' *)
    if not (BT.is_proper_desc k k') then Failed
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

let has_instore_merkle_desc (st: vstore) (k:key{contains_key st k}): bool = 
  if K.is_data_key k then false
  else 
    let v = R.to_merkle_value (value_of st k) in
    let ld = R.desc_hash_dir v BT.Left in
    let rd = R.desc_hash_dir v BT.Right in
    R.Desc? ld && is_instore_madd st (R.Desc?.k ld) || 
    R.Desc? rd && is_instore_madd st (R.Desc?.k rd)

let vevictm (s s':slot_id) (vs: vtls {Valid? vs}): vtls = 
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
    (* check k is a proper descendent of k' *)
    if not (BT.is_proper_desc k k') then Failed
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

let vaddb (s:slot_id) (r:record) (t:timestamp) (j:thread_id) (vs:vtls {Valid? vs}): vtls = 
  let st = thread_store vs in 
  if not (s < Seq.length st.data) then Failed
  (* epoch of timestamp of last evict *)
  else 
    let e = MHD.MkTimestamp?.e t in
    let k = Record?.k r in
    let v = Record?.v r in
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

let vevictb (s:slot_id) (t:timestamp) (vs:vtls {Valid? vs}): vtls = 
  let clock = thread_clock vs in
  let e = MHD.MkTimestamp?.e t in
  let st = thread_store vs in
  (* check store contains slot s *)
  if not (contains_record st s) then Failed
  else
    let k = get_key_at st s in
    let v = get_value_at st s in
    (* check key at s is not root *)
    if k = BT.Root then Failed
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

let vevictbm (s s':slot_id) (t:timestamp) (vs:vtls {Valid? vs}): vtls = 
  let st = thread_store vs in
  (* check store contains s and s' *)
  if not (contains_record st s && contains_record st s') then Failed
  else
    let k = get_key_at st s in
    let k' = get_key_at st s' in
    let v' = get_value_at st s' in
    (* check k is a proper desc of k' *)
    if not (BT.is_proper_desc k k') then Failed
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
                            vevictb s t (update_thread_store vs st_upd)

(* thread-level verification step
   (following the defn in Veritas.Verifier) *)
let t_verify_step (vs:vtls)
                  (e:vlog_entry): vtls =                           
  match vs with
  | Failed -> Failed (* could check the is_map flag here *)
  | _ ->
    match e with
    | Get s v -> vget s v vs
    | Put s v -> vput s v vs
    | AddM s r s'  -> vaddm s r s' vs
    | EvictM s s' -> vevictm s s' vs
    | AddB s r t j -> vaddb s r t j vs
    | EvictB s t -> vevictb s t vs
    | EvictBM s s' t -> vevictbm s s' t vs

let vlog = Seq.seq vlog_entry

(* verify a log from a specified initial state *)
let rec t_verify_aux (vs:vtls) (l:vlog): Tot vtls
  (decreases (Seq.length l)) =
  let n = Seq.length l in
  if n = 0 then vs
  else
    let l' = SA.prefix l (n - 1) in
    let vs' = t_verify_aux vs l' in
    let e' = Seq.index l (n - 1) in
    t_verify_step vs' e'

// TODO: what should the initial size be? a parameter? some contant?
let empty_store:vstore = { data=Seq.create 10 None; is_map=true }

(* initialize verifier state *)
let init_thread_state (id:thread_id): vtls = 
  let vs = Valid id empty_store (MHD.MkTimestamp 0 0) MHD.empty_hash_value MHD.empty_hash_value in  
  if id = 0 then
    let st0 = thread_store vs in
    // TODO: where should we stick the root?
    let st0_upd = add_record st0 0 BT.Root (R.init_value BT.Root) V.MAdd in
    update_thread_store vs st0_upd    
  else vs

let t_verify (id:thread_id) (l:vlog): vtls = 
  t_verify_aux (init_thread_state id) l 

let verifiable (id:thread_id) (l: vlog): bool =
  let vs = t_verify id l in
  if Valid? vs 
  then let st = Valid?.st vs in st.is_map
  else false
