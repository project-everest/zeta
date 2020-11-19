module Veritas.Intermediate.VerifyS

open Veritas.Intermediate.Logs
open Veritas.Intermediate.StoreS

open Veritas.BinTree
open Veritas.Hash
open Veritas.Key
open Veritas.MultiSetHash
open Veritas.MultiSetHashDomain
open Veritas.Record
open Veritas.SeqAux

module Spec = Veritas.Verifier
module SC = Veritas.Intermediate.VerifySC
module SCstore = Veritas.Intermediate.StoreSC

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
    hadd : ms_hash_value -> // TODO: should be a multiset
    hevict : ms_hash_value -> // TODO: should be a (multi?)set
    vtls

let thread_id_of (vs:vtls {Valid? vs}): thread_id = 
  Valid?.id vs

let thread_store (vs: vtls {Valid? vs}): vstore =
  Valid?.st vs

let thread_store_size (vs: vtls {Valid? vs}): nat =
  let st = thread_store vs in Seq.length st

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

let update_thread_hadd (vs:vtls {Valid? vs}) (hadd: ms_hash_value): vtls = 
  match vs with
  | Valid id st clock _ hevict -> Valid id st clock hadd hevict

let update_thread_hevict (vs:vtls {Valid? vs}) (hevict:ms_hash_value): vtls = 
  match vs with
  | Valid id st clock hadd _ -> Valid id st clock hadd hevict

let vget (s:slot_id) (k:key) (v:data_value) (vs: vtls {Valid? vs}) : vtls =
  let st = thread_store vs in
  (* check store contains slot s *)
  if not (store_contains st s) then Failed
  (* check stored key and value *)
  else let k' = stored_key st s in
       let v' = stored_value st s in
       if k <> k' then Failed
       else if not (DVal? v') then Failed
       else if to_data_value v' <> v then Failed
       else vs

let vput (s:slot_id) (k:key) (v:data_value) (vs: vtls {Valid? vs}) : vtls =
  let st = thread_store vs in
  (* check store contains slot s *)
  if not (store_contains st s) then Failed
  (* check stored key is k *)
  else let k' = stored_key st s in
       if k <> k' then Failed
       else if not (is_data_key (stored_key st s)) then Failed
       else update_thread_store vs (update_value st s (DVal v))

let vaddm (s:slot_id) (r:record) (s':slot_id) (vs: vtls {Valid? vs}): vtls =
  if not (s < thread_store_size vs) then Failed
  else 
    let st = thread_store vs in
    let (k,v) = r in
    (* check store contains slot s' *)
    if not (store_contains st s') then Failed
    else
      let k' = stored_key st s' in
      let v' = stored_value st s' in
      (* check k is a proper desc of k' *)
      if not (is_proper_desc k k') then Failed
      (* check store does not contain slot s *)
      else if store_contains st s then Failed
      (* check type of v is consistent with k *)
      else if not (is_value_of k v) then Failed
      (* check v' is a merkle value *)
      else if DVal? v' then Failed 
      else
        let v' = to_merkle_value v' in
        let d = desc_dir k k' in
        let dh' = desc_hash_dir v' d in 
        let h = hashfn v in
        match dh' with
        | Empty -> (* k' has no child in direction d *)
            (* first add must be init value *)
            if v <> init_value k then Failed
            else
              let v'_upd = Spec.update_merkle_value v' d k h false in
              let st_upd = update_value st s' (MVal v'_upd) in
              let st_upd2 = add_to_store st_upd s k v Spec.MAdd in
              let st_upd3 = update_in_store st_upd2 s' d true in
              update_thread_store vs st_upd3
        | Desc k2 h2 b2 -> 
            if k2 = k 
            then (* k is a child of k' *)
              (* check hashes match and k was not evicted to blum *)
              if not (h2 = h && b2 = false) then Failed
              (* check store does not contain k*)
              else if child_in_store st s' d then Failed
              else 
                let st_upd = add_to_store st s k v Spec.MAdd in
                let st_upd2 = update_in_store st_upd s' d true in
                update_thread_store vs st_upd2
            else (* otherwise, k is not a child of k' *)
            (* first add must be init value *)
            if v <> init_value k then Failed
            (* check k2 is a proper desc of k *)
            else if not (is_proper_desc k2 k) then Failed
            else
              let d2 = desc_dir k2 k in
              let mv = to_merkle_value v in
              let mv_upd = Spec.update_merkle_value mv d2 k2 h2 b2 in
              let v'_upd = Spec.update_merkle_value v' d k h false in
              let st_upd = update_value st s' (MVal v'_upd) in
              let st_upd2 = add_to_store st_upd s k (MVal mv_upd) Spec.MAdd in
              let st_upd3 = update_in_store st_upd2 s' d true in
              let st_upd4 = update_in_store st_upd3 s d2 true in
              update_thread_store vs st_upd4

let has_instore_merkle_desc (st:vstore) (s:slot_id{store_contains st s}): bool = 
  let k = stored_key st s in
  if is_data_key k then false
  else 
    // TODO: remove the assert with a better SMTPat for stored_value_matches_stored_key
    let _ = assert (is_value_of k (stored_value st s)) in   
    let v = to_merkle_value (stored_value st s) in
    let ld = desc_hash_dir v Left in
    let rd = desc_hash_dir v Right in
    Desc? ld && l_child_in_store st s || 
    Desc? rd && r_child_in_store st s

let update_hash_and_blum_bit 
      (st:vstore) 
      (s:slot_id{store_contains st s /\ MVal? (stored_value st s)}) 
      (d:bin_tree_dir{Desc? (desc_hash_dir (to_merkle_value (stored_value st s)) d)}) 
      (h:hash_value)
      (b:bool)
  : vstore
  = let mv = to_merkle_value (stored_value st s) in
    let Desc k _ _ = desc_hash_dir mv d in
    let mv' = Spec.update_merkle_value mv d k h b in
    update_value st s (MVal mv')

let vevictm (s:slot_id) (s':slot_id) (vs: vtls {Valid? vs}): vtls = 
  let st = thread_store vs in
  (* check store contains s and s' *)
  if not (store_contains st s && store_contains st s') then Failed
  else 
    let k = stored_key st s in
    let v = stored_value st s in
    let k' = stored_key st s' in
    let v' = stored_value st s' in
    (* check k is a proper descendent of k' *)
    if not (is_proper_desc k k') then Failed
    (* check k does not have a child in the store *)
    else if has_instore_merkle_desc st s then Failed
    else
      let d = desc_dir k k' in
      // TODO: remove the assert with a better SMTPat for stored_value_matches_stored_key
      let _ = assert (is_value_of k' v') in 
      let v' = to_merkle_value v' in
      let dh' = desc_hash_dir v' d in
      let h = hashfn v in
      match dh' with
      | Empty -> Failed
      | Desc k2 h2 b2 -> 
          if k2 <> k then Failed
          else
            let st_upd = update_hash_and_blum_bit st s' d h false in
            let st_upd2 = evict_from_store st_upd s in
            update_thread_store vs st_upd2

let vaddb (s:slot_id) (r:record) (t:timestamp) (j:thread_id) (vs:vtls {Valid? vs}): vtls = 
  if not (s < thread_store_size vs) then Failed
  else
    let st = thread_store vs in 
    let (k,v) = r in
    (* check value type consistent with key k *)
    if not (is_value_of k v) then Failed
    (* check store contains slot s *)
    else if store_contains st s then Failed
    else 
      (* update add hash *)
      let h = thread_hadd vs in
      let h_upd = ms_hashfn_upd (MHDom (k,v) t j) h in
      let vs_upd = update_thread_hadd vs h_upd in
      (* update clock *)
      let clk = thread_clock vs in
      let clk_upd = Spec.max clk (next t) in
      let vs_upd2 = update_thread_clock vs_upd clk_upd in
      (* add record to store *)
      let st_upd = add_to_store st s k v Spec.BAdd in
      update_thread_store vs_upd2 st_upd

let vevictb (s:slot_id) (t:timestamp) (vs:vtls {Valid? vs}): vtls = 
  let clock = thread_clock vs in
  let st = thread_store vs in
  (* check store contains slot s *)
  if not (store_contains st s) then Failed
  else
    let k = stored_key st s in
    let v = stored_value st s in
    (* check key at s is not root *)
    if k = Root then Failed
    (* check time of evict < current time *)
    else if not (ts_lt clock t) then Failed
    (* check s was added through blum *)  
    else if add_method_of st s <> Spec.BAdd then Failed
    (* check k has no children n the store *)
    else if has_instore_merkle_desc st s then Failed  
    else 
      (* update evict hash *)
      let h = thread_hevict vs in
      let h_upd = ms_hashfn_upd (MHDom (k,v) t (thread_id_of vs)) h in
      let vs_upd = update_thread_hevict vs h_upd in
      (* update clock *)
      let vs_upd2 = update_thread_clock vs_upd t in    
      (* evict record *)
      let st_upd = evict_from_store st s in
      update_thread_store vs_upd2 st_upd

let vevictbm (s:slot_id) (s':slot_id) (t:timestamp) (vs:vtls {Valid? vs}): vtls = 
  let st = thread_store vs in
  (* check store contains s and s' *)
  if not (store_contains st s && store_contains st s') then Failed
  else
    let k = stored_key st s in
    let k' = stored_key st s' in
    let v' = stored_value st s' in
    (* check k is a proper desc of k' *)
    if not (is_proper_desc k k') then Failed
    (* check s was added through merkle *)
    else if add_method_of st s <> Spec.MAdd then Failed  
    (* check k has no children in the store *)
    else if has_instore_merkle_desc st s then Failed  
    else
      // TODO: remove the assert with a better SMTPat for stored_value_matches_stored_key
      let _ = assert (is_value_of k' v') in 
      let v' = to_merkle_value v' in
      let d = desc_dir k k' in
      let dh' = desc_hash_dir v' d in
      match dh' with
      | Empty -> Failed
      | Desc k2 h2 b2 -> 
          if k2 <> k || b2 then Failed
          else
            let st_upd = update_hash_and_blum_bit st s' d h2 true in
            vevictb s t (update_thread_store vs st_upd)

(* Relation between SC and S thread-local states *)
  
let vtls_rel (vs:vtls) (vs':SC.vtls) : Type =
  (Failed? vs /\ SC.Failed? vs') \/
  (Valid? vs /\ SC.Valid? vs' /\
   (let (Valid id st clk ha he) = vs in
    let (SC.Valid id' st' clk' ha' he') = vs' in
    // all fields are equal
    equal_contents st st' /\ id = id' /\ clk = clk' /\ ha = ha' /\ he = he' /\
    // the invariant over MAdd keys holds
    merkle_store_inv st))

let lemma_vget_simulates_SC 
      (vs:vtls{Valid? vs})
      (vs':SC.vtls{SC.Valid? vs'})
      (s:slot_id)
      (k:data_key)
      (v:data_value)
  : Lemma (requires (vtls_rel vs vs'))
          (ensures (vtls_rel (vget s k v vs) (SC.vget s k v vs')))
  = ()

let lemma_update_value_DVal_preserves_merkle_inv (st:vstore) (s:slot_id{store_contains st s /\ is_data_key (stored_key st s)}) (v:data_value)
  : Lemma (requires merkle_store_inv st)
          (ensures merkle_store_inv (update_value st s (DVal v)))
          [SMTPat (merkle_store_inv (update_value st s (DVal v)))]
  = admit()

let lemma_vput_simulates_SC
      (vs:vtls{Valid? vs}) 
      (vs':SC.vtls{SC.Valid? vs'}) 
      (s:slot_id) 
      (k:data_key) 
      (v:data_value) 
  : Lemma (requires (vtls_rel vs vs'))
          (ensures (vtls_rel (vput s k v vs) (SC.vput s k v vs'))) 
  = ()

#push-options "--z3rlimit_factor 2"
let lemma_vaddm_simulates_SC 
      (vs:vtls{Valid? vs}) 
      (vs':SC.vtls{SC.Valid? vs'}) 
      (s s':slot_id)
      (r:record)  
  : Lemma (requires (vtls_rel vs vs'))
          (ensures (vtls_rel (vaddm s r s' vs) (SC.vaddm s r s' vs'))) 
  = if s < thread_store_size vs
    then 
      let st = thread_store vs in
      let (k,v) = r in
      if store_contains st s'
      then
        let k' = stored_key st s' in
        let v' = stored_value st s' in
        if is_proper_desc k k' && not (store_contains st s) && is_value_of k v && not (DVal? v')
        then
          let v' = to_merkle_value v' in
          let d = desc_dir k k' in
          let dh' = desc_hash_dir v' d in 
          let h = hashfn v in
          let st' = SC.thread_store vs' in
          match dh' with
          | Empty -> 
              // CASE 1 - by points_to_nearest_desc_in_store, either k is not in the store or 
              //          the final hash check is guaranteed to fail
              assert (points_to_nearest_desc_in_store st s');
              if v = init_value k 
              then (
                let v'_upd = Spec.update_merkle_value v' d k h false in
                let st_upd = update_value st s' (MVal v'_upd) in
                let st_upd2 = add_to_store st_upd s k v Spec.MAdd in
                let st_upd3 = update_in_store st_upd2 s' d true in
                assume (merkle_store_inv st_upd3)
              )
          | Desc k2 h2 b2 -> 
              if k2 = k 
              // CASE 2 - by in_store_flag_implies.. and evicted_to_blum_flag_implies.., either 
              //          k is not in the store or the final hash check is guaranteed to fail
              then (
                assert (in_store_flag_unset_equals_desc_not_in_store st s');              
                if h2 = h && b2 = false
                then 
                if not (child_in_store st s' d)
                then (
                  assert (not (store_contains_key_with_MAdd st k));
                  let st_upd = add_to_store st s k v Spec.MAdd in
                  let st_upd2 = update_in_store st_upd s' d true in
                  assume (merkle_store_inv st_upd2)
                )
              )
              // CASE 3 - similar to CASE 1
              else (
                assert (points_to_nearest_desc_in_store st s');              
                if v = init_value k && is_proper_desc k2 k 
                then
                  let d2 = desc_dir k2 k in
                  let mv = to_merkle_value v in
                  let mv_upd = Spec.update_merkle_value mv d2 k2 h2 b2 in
                  let v'_upd = Spec.update_merkle_value v' d k h false in
                  let st_upd = update_value st s' (MVal v'_upd) in
                  let st_upd2 = add_to_store st_upd s k (MVal mv_upd) Spec.MAdd in
                  let st_upd3 = update_in_store st_upd2 s' d true in
                  let st_upd4 = update_in_store st_upd3 s d2 true in
                  assume (merkle_store_inv st_upd4)
              )
#pop-options

let lemma_evict_from_store_preserves_inv (st:vstore) (s:slot_id{store_contains st s})
  : Lemma (requires merkle_store_inv st)
          (ensures merkle_store_inv (evict_from_store st s))
          [SMTPat (merkle_store_inv (evict_from_store st s))]
  = admit()

let lemma_has_in_store_merkle_desc (st:vstore) (st':SCstore.vstore) (s:slot_id{store_contains st s})
  : Lemma (requires equal_contents st st' /\ merkle_store_inv st)
          (ensures has_instore_merkle_desc st s = SC.has_instore_merkle_desc st' (SCstore.stored_key st' s))
          [SMTPat (has_instore_merkle_desc st s); SMTPat (SC.has_instore_merkle_desc st' (SCstore.stored_key st' s))]
  = admit()

let lemma_update_hash_and_blum_bit_preserves_inv 
      (st:vstore) 
      (s:slot_id{store_contains st s /\ MVal? (stored_value st s)}) 
      (d:bin_tree_dir{Desc? (desc_hash_dir (to_merkle_value (stored_value st s)) d)}) 
      (h:hash_value)
      (b:bool)
  : Lemma (requires merkle_store_inv st)
          (ensures merkle_store_inv (update_hash_and_blum_bit st s d h b)) 
          [SMTPat (merkle_store_inv (update_hash_and_blum_bit st s d h b))]
  = admit()

let lemma_vevictm_simulates_SC 
      (vs:vtls{Valid? vs}) 
      (vs':SC.vtls{SC.Valid? vs'}) 
      (s s':slot_id)  
  : Lemma (requires (vtls_rel vs vs'))
          (ensures (vtls_rel (vevictm s s' vs) (SC.vevictm s s' vs'))) 
  = ()

let lemma_add_to_store_BAdd_preserves_inv (st:vstore) (s:st_index st{not (store_contains st s)}) (k:key) (v:value_type_of k)
  : Lemma (requires merkle_store_inv st)
          (ensures merkle_store_inv (add_to_store st s k v Spec.BAdd))
          [SMTPat (merkle_store_inv (add_to_store st s k v Spec.BAdd))]
  = admit()

let lemma_vaddb_simulates_SC 
      (vs:vtls{Valid? vs}) 
      (vs':SC.vtls{SC.Valid? vs'}) 
      (s:slot_id)
      (r:record)
      (t:timestamp)
      (j:thread_id)
  : Lemma (requires (vtls_rel vs vs'))
          (ensures (vtls_rel (vaddb s r t j vs) (SC.vaddb s r t j vs')))
  = ()

let lemma_vevictb_simulates_SC 
      (vs:vtls{Valid? vs}) 
      (vs':SC.vtls{SC.Valid? vs'}) 
      (s:slot_id)
      (t:timestamp)
  : Lemma (requires (vtls_rel vs vs'))
          (ensures (vtls_rel (vevictb s t vs) (SC.vevictb s t vs'))) 
          [SMTPat (vtls_rel (vevictb s t vs) (SC.vevictb s t vs'))]
  = ()

let lemma_vevictbm_simulates_SC 
      (vs:vtls{Valid? vs}) 
      (vs':SC.vtls{SC.Valid? vs'}) 
      (s s':slot_id)
      (t:timestamp)
  : Lemma (requires (vtls_rel vs vs'))
          (ensures (vtls_rel (vevictbm s s' t vs) (SC.vevictbm s s' t vs'))) 
  = ()
  
let t_verify_step (vs:vtls) (e:logS_entry): vtls =
  match vs with
  | Failed -> Failed
  | _ ->
    match e with
    | Get_S s k v -> vget s k v vs
    | Put_S s k v -> vput s k v vs
    | AddM_S s r s' -> vaddm s r s' vs
    | EvictM_S s s' -> vevictm s s' vs
    | AddB_S s r t j -> vaddb s r t j vs
    | EvictB_S s t -> vevictb s t vs
    | EvictBM_S s s' t -> vevictbm s s' t vs

(* Verify a (thread-local) log from a specified initial state *)
let rec t_verify_aux (vs:vtls) (l:logS): Tot vtls
  (decreases (Seq.length l)) =
  let n = Seq.length l in
  if n = 0 then vs
  else
    let lp = prefix l (n - 1) in
    let vsp = t_verify_aux vs lp in
    let e = Seq.index l (n - 1) in
    t_verify_step vsp e

(* Initialize verifier state *)
// TODO: what should the initial size be?
let store_size = 65536 // 2 ^ 16
let init_thread_state (id:thread_id): vtls = 
  let vs = Valid id (empty_store store_size) (MkTimestamp 0 0) empty_hash_value empty_hash_value in  
  if id = 0 then
    let st0 = thread_store vs in
    let st0_upd = add_to_store st0 0 Root (init_value Root) Spec.MAdd in
    update_thread_store vs st0_upd    
  else vs

(* Main thread-level verify function *)
let t_verify (id:thread_id) (l:logS): vtls = 
  t_verify_aux (init_thread_state id) l 

val init_thread_state_valid (id:thread_id)
  : Lemma (Valid? (init_thread_state id))
          [SMTPat (init_thread_state id)]

val lemma_init_thread_state_rel (id:thread_id)
  : Lemma (vtls_rel (init_thread_state id) (SC.init_thread_state id))

val lemma_t_verify_simulates_SC (id:thread_id) (l:logS) 
  : Lemma (vtls_rel (t_verify id l) (SC.t_verify id l))

(* Global verification *)
let verify (tl:thread_id_logS): vtls =
  t_verify (fst tl) (snd tl)
  
let verifiable (gl: g_logS) = 
  forall (tid:seq_index gl). Valid? (verify (thread_log gl tid))

let verifiable_log = gl:g_logS{verifiable gl}

val hadd (gl: verifiable_log): ms_hash_value

val hevict (gl: verifiable_log): ms_hash_value

let hash_verifiable (gl: verifiable_log): bool = 
  hadd gl = hevict gl

let hash_verifiable_log = gl:verifiable_log{hash_verifiable gl}

let lemma_verifiable_simulates_SC (gl:verifiable_log)
  : Lemma (ensures SC.verifiable gl)
          [SMTPat (SC.verifiable gl)]
  = admit()

let lemma_hash_verifiable_simulates_SC (gl:hash_verifiable_log)
  : Lemma (SC.hash_verifiable gl)
  = admit() 
    // requires showing that hash check succeeds ==> SC returns is_map=true for every thread
    // alternatively, if SC returns is_map=false for any thread, then the hash check will fail

(* Correctness *)

let lemma_verifier_correct (gl: hash_verifiable_log { ~ (Veritas.State.seq_consistent (to_state_op_glogS gl))})
  : Veritas.Verifier.EAC.hash_collision_gen
  = lemma_hash_verifiable_simulates_SC gl;
    SC.lemma_verifier_correct gl
