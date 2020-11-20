module Veritas.Intermediate.VerifySC

open Veritas.Intermediate.Logs
open Veritas.Intermediate.StoreSC

(* These are all independent of the 'verify' function; they should be safe to open *)
open Veritas.BinTree
open Veritas.Hash
open Veritas.Key
open Veritas.MultiSetHash
open Veritas.MultiSetHashDomain
open Veritas.Record
open Veritas.SeqAux

(* It's better not to open these modules to avoid naming conflicts *)
module Spec = Veritas.Verifier
module SpecVT = Veritas.Verifier.Thread
module SpecVG = Veritas.Verifier.Global
module SpecVC = Veritas.Verifier.Correctness

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
    hadd : ms_hash_value ->
    hevict : ms_hash_value ->
    vtls

let thread_id_of (vs:vtls {Valid? vs}): thread_id = 
  Valid?.id vs

let thread_store (vs: vtls {Valid? vs}): vstore =
  Valid?.st vs

let thread_store_is_map (vs: vtls {Valid? vs}): bool =
  let st = thread_store vs in st.is_map

let thread_store_size (vs: vtls {Valid? vs}): nat =
  let st = thread_store vs in Seq.length st.data

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
       else update_thread_store vs (update_store st s (DVal v))

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
      (* check store does not contain key k via MAdd
         >> in lower levels we will check this via 'in_store' fields *)
      else if store_contains_key st k && add_method_of_by_key st k = Spec.MAdd then Failed
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
              let st_upd = update_store st s' (MVal v'_upd) in
              let st_upd2 = add_to_store st_upd s k v Spec.MAdd in
              update_thread_store vs st_upd2
        | Desc k2 h2 b2 -> 
            if k2 = k 
            then (* k is a child of k' *)
              (* check hashes match and k was not evicted to blum *)
              if not (h2 = h && b2 = false) then Failed
              else update_thread_store vs (add_to_store st s k v Spec.MAdd)
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
              let st_upd = update_store st s' (MVal v'_upd) in
              let st_upd2 = add_to_store st_upd s k (MVal mv_upd) Spec.MAdd in
              update_thread_store vs st_upd2

(* key k is in store and was added using Merkle *)
let is_instore_madd (st: vstore) (k: key): bool = 
  store_contains_key st k && 
  add_method_of_by_key st k = Spec.MAdd

let has_instore_merkle_desc (st:vstore) (k:key{store_contains_key st k}): bool = 
  if is_data_key k then false
  else 
    let v = to_merkle_value (stored_value_by_key st k) in
    let ld = desc_hash_dir v Left in
    let rd = desc_hash_dir v Right in
    Desc? ld && is_instore_madd st (Desc?.k ld) || 
    Desc? rd && is_instore_madd st (Desc?.k rd)

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
    else if has_instore_merkle_desc st k then Failed
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
            let v'_upd = Spec.update_merkle_value v' d k h false in
            let st_upd = update_store st s' (MVal v'_upd) in
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
    else if has_instore_merkle_desc st k then Failed  
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
    else if has_instore_merkle_desc st k then Failed  
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
            let v'_upd = Spec.update_merkle_value v' d k h2 true in
            let st_upd = update_store st s' (MVal v'_upd) in
            vevictb s t (update_thread_store vs st_upd)

(* Relation between thread-local states *)
let has_failed (vs:vtls) = Failed? vs || not (thread_store_is_map vs)
let vtls_rel (vs:vtls) (vs':Spec.vtls) : Type =
  if has_failed vs then Spec.Failed? vs'
  else 
    match vs, vs' with
    | Valid id st clk ha he, Spec.Valid id' st' clk' _ ha' he' ->
        store_rel st st' /\ 
        // other fields related by equality  
        id = id' /\ clk = clk' /\ ha = ha' /\ he = he'   
    | _, _ -> False

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

val logS_to_logK_entry (vs:vtls{Valid? vs}) (e:logS_entry) : option logK_entry

let add_to_log (l:option logK) (vs:vtls) (e:logS_entry) : option logK =
  if Some? l && Valid? vs && Some? (logS_to_logK_entry vs e)
  then Some (append1 (Some?.v l) (Some?.v (logS_to_logK_entry vs e)))
  else None

(* Verify a log from a specified initial state; also returns the
   corresponding log with keys *)
let rec t_verify_aux (vs:vtls) (l:logS): Tot (vtls * option logK)
  (decreases (Seq.length l)) =
  let n = Seq.length l in
  if n = 0 then (vs, Some Seq.empty)
  else
    let lp = prefix l (n - 1) in
    let (vsp,lk) = t_verify_aux vs lp in
    let e = Seq.index l (n - 1) in
    let vs' = t_verify_step vsp e in
    let lk' = add_to_log lk vsp e in
    (vs', lk')

val lemma_t_verify_aux_valid_implies_log_exists (vs:vtls) (l:logS)
  : Lemma (requires (Valid? (fst (t_verify_aux vs l))))
          (ensures (Some? (snd (t_verify_aux vs l))))
          (decreases (Seq.length l))
          [SMTPat (Some? (snd (t_verify_aux vs l)))]

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
  fst (t_verify_aux (init_thread_state id) l) 

let logS_to_logK (id:thread_id) (l:logS{Valid? (t_verify id l)}) : logK =
  Some?.v (snd (t_verify_aux (init_thread_state id) l))

let init_thread_state_valid (id:thread_id)
  : Lemma (Valid? (init_thread_state id))
          [SMTPat (init_thread_state id)]
  = ()

val lemma_init_thread_state_rel (id:thread_id) :
  Lemma (vtls_rel (init_thread_state id) (Spec.init_thread_state id))

val lemma_t_verify_simulates_spec (id:thread_id) (l:logS) 
  : Lemma (requires (Valid? (t_verify id l)))
          (ensures (vtls_rel (t_verify id l) (Spec.t_verify id (logS_to_logK id l))))

val lemma_logS_to_logK_to_state_op (id:thread_id) (l:logS{Valid? (t_verify id l)})
  : Lemma (ensures (Seq.equal (to_state_op_logS l) 
                              (Veritas.EAC.to_state_op_vlog (logS_to_logK id l))))
           [SMTPat (Veritas.EAC.to_state_op_vlog (logS_to_logK id l))]

(* Global verification following the definitions in Veritas.Verifier.Thread and 
   Veritas.Verifier.Global *) 

let verify (tl:thread_id_logS): vtls =
  t_verify (fst tl) (snd tl)
  
let verifiable (gl: g_logS) = 
  forall (tid:seq_index gl). Valid? (verify (thread_log gl tid))

let verifiable_log = gl:g_logS{verifiable gl}

val lemma_prefix_verifiable (gl: verifiable_log) (i:seq_index gl)
  : Lemma (ensures verifiable (prefix gl i))
          [SMTPat (verifiable (prefix gl i))]

let rec hadd_aux (gl: verifiable_log)
  : Tot (ms_hash_value)
    (decreases (Seq.length gl)) 
  = let p = Seq.length gl in
    if p = 0 then empty_hash_value
    else
      let gl' = prefix gl (p - 1) in
      let h1 = hadd_aux gl' in
      let h2 = thread_hadd (verify (thread_log gl (p - 1))) in
      ms_hashfn_agg h1 h2

let hadd (gl: verifiable_log): ms_hash_value = hadd_aux gl

let rec hevict_aux (gl: verifiable_log)
  : Tot (ms_hash_value)
    (decreases (Seq.length gl))
  = let p = Seq.length gl in
    if p = 0 then empty_hash_value
    else
      let gl' = prefix gl (p - 1) in
      let h1 = hevict_aux gl' in
      let h2 = thread_hevict (verify (thread_log gl (p - 1))) in
      ms_hashfn_agg h1 h2

let hevict (gl: verifiable_log): ms_hash_value = hevict_aux gl

val forall_is_map (gl:verifiable_log) : bool

let hash_verifiable (gl: verifiable_log): bool = 
  hadd gl = hevict gl && forall_is_map gl

let hash_verifiable_log = gl:verifiable_log{hash_verifiable gl}

val glogS_to_logK (gl:verifiable_log{forall_is_map gl}) : gl':SpecVG.verifiable_log{Seq.length gl = Seq.length gl'}

val lemma_glogS_to_logK (gl:verifiable_log{forall_is_map gl}) (id:seq_index gl)
  : Lemma (ensures Seq.index (glogS_to_logK gl) id = logS_to_logK id (Seq.index gl id))
          [SMTPat (Seq.index (glogS_to_logK gl) id)]

val hadd_values_equal (gl:verifiable_log{forall_is_map gl}) 
  : Lemma (hadd gl = SpecVG.hadd (glogS_to_logK gl))

val hevict_values_equal (gl:verifiable_log{forall_is_map gl}) 
  : Lemma (hevict gl = SpecVG.hevict (glogS_to_logK gl))

let lemma_hash_verifiable_simulates_spec (gl:hash_verifiable_log)
  : Lemma (SpecVG.hash_verifiable (glogS_to_logK gl))
  = hadd_values_equal gl;
    hevict_values_equal gl

(* Final correctness theorem, following the definition in Veritas.Verifier.Correctness *)

let lemma_to_state_op_glogS (gl: verifiable_log{forall_is_map gl})
  : Lemma (ensures (Seq.equal (to_state_op_glogS gl) 
                              (SpecVC.to_state_op_gvlog (glogS_to_logK gl))))
  = let aux (i:seq_index gl) 
      : Lemma (Seq.index (to_state_op_glogS gl) i = 
              Seq.index (SpecVC.to_state_op_gvlog (glogS_to_logK gl)) i)
      = () in
    Classical.forall_intro aux

let lemma_verifier_correct (gl: hash_verifiable_log { ~ (Veritas.State.seq_consistent (to_state_op_glogS gl))})
  : Veritas.Verifier.EAC.hash_collision_gen
  = let gl' = glogS_to_logK gl in
    lemma_hash_verifiable_simulates_spec gl;
    lemma_to_state_op_glogS gl;
    SpecVC.lemma_verifier_correct gl'
