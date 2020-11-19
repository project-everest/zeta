module Veritas.Intermediate.VerifySC

let lemma_vget_simulates_spec 
      (vs:vtls{Valid? vs})
      (vs':Spec.vtls{Spec.Valid? vs'})
      (s:slot_id)
      (k:data_key)
      (v:data_value)
  : Lemma (requires (vtls_rel vs vs' /\ slot_key_rel vs s k))
          (ensures (vtls_rel (vget s k v vs) (Spec.vget k v vs')))
  = ()
  
let lemma_vget_has_failed (vs:vtls{Valid? vs}) (s:slot_id) (k:key) (v:data_value)
  : Lemma (requires (not (thread_store_is_map vs)))
          (ensures (has_failed (vget s k v vs)))
  = ()

let lemma_vput_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s:slot_id) 
      (k:data_key) 
      (v:data_value) 
  : Lemma (requires (vtls_rel vs vs' /\ slot_key_rel vs s k))
          (ensures (vtls_rel (vput s k v vs) (Spec.vput k v vs'))) 
  = ()

let lemma_vput_has_failed (vs:vtls{Valid? vs}) (s:slot_id) (k:key) (v:data_value)
  : Lemma (requires (not (thread_store_is_map vs)))
          (ensures (has_failed (vput s k v vs)))
  = ()

// TODO: flaky; can we pick better SMTPats?
#push-options "--z3rlimit_factor 2"
let lemma_vaddm_simulates_spec
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s s':slot_id)
      (r:record)
      (k':merkle_key)  
   : Lemma (requires (s < thread_store_size vs /\
                      not (store_contains (thread_store vs) s) /\
                      vtls_rel vs vs' /\ 
                      slot_key_rel vs s' k'))
           (ensures (vtls_rel (vaddm s r s' vs) (Spec.vaddm r k' vs'))) 
  = ()
#pop-options

let lemma_vaddm_has_failed (vs:vtls{Valid? vs}) (s s':slot_id) (r:record)
  : Lemma (requires (not (thread_store_is_map vs)))
          (ensures (has_failed (vaddm s r s' vs)))
  = ()

let lemma_vevictm_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s s':slot_id)
      (k:key)
      (k':merkle_key)  
  : Lemma (requires (vtls_rel vs vs' /\ slot_key_rel vs s k /\ slot_key_rel vs s' k'))
          (ensures (vtls_rel (vevictm s s' vs) (Spec.vevictm k k' vs'))) 
  = () 

let lemma_vevictm_has_failed (vs:vtls{Valid? vs}) (s s':slot_id)
  : Lemma (requires (not (thread_store_is_map vs)))
          (ensures (has_failed (vevictm s s' vs)))
  = let st = thread_store vs in
    if store_contains st s'
    then // TODO: get this lemma to trigger automatically 
      stored_value_matches_stored_key st s'

let lemma_vaddb_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s:slot_id)
      (r:record)
      (t:timestamp)
      (j:thread_id)
  : Lemma (requires (s < thread_store_size vs /\ 
                     not (store_contains (thread_store vs) s) /\ 
                     vtls_rel vs vs'))
          (ensures (vtls_rel (vaddb s r t j vs) (Spec.vaddb r t j vs')))
  = ()

let lemma_vaddb_has_failed (vs:vtls{Valid? vs}) (s:slot_id) (r:record) (t:timestamp) (j:thread_id)
  : Lemma (requires (not (thread_store_is_map vs)))
          (ensures (has_failed (vaddb s r t j vs)))
  = ()

let lemma_vevictb_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s:slot_id)
      (k:key)
      (t:timestamp)
  : Lemma (requires (vtls_rel vs vs' /\ slot_key_rel vs s k))
          (ensures (vtls_rel (vevictb s t vs) (Spec.vevictb k t vs'))) 
  = ()

let lemma_vevictb_has_failed (vs:vtls{Valid? vs}) (s:slot_id) (t:timestamp)
  : Lemma (requires (not (thread_store_is_map vs)))
          (ensures (has_failed (vevictb s t vs)))
  =  ()

let lemma_vevictbm_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s s':slot_id)
      (k:key)
      (k':merkle_key)
      (t:timestamp)
  : Lemma (requires (vtls_rel vs vs' /\ slot_key_rel vs s k /\ slot_key_rel vs s' k'))
          (ensures (vtls_rel (vevictbm s s' t vs) (Spec.vevictbm k k' t vs'))) 
  = ()
  
let lemma_vevictbm_has_failed (vs:vtls{Valid? vs}) (s s':slot_id) (t:timestamp)
  : Lemma (requires (not (thread_store_is_map vs)))
          (ensures (has_failed (vevictbm s s' t vs)))
  = let st = thread_store vs in
    if store_contains st s'
    then // TODO: get this lemma to trigger automatically 
      stored_value_matches_stored_key st s'

(* This is basically a "light" versions of the vfun functions to reconstruct the log. 
   We could have the vfun functions return logK entries instead, but this seems cleaner. *)
let logS_to_logK_entry (vs:vtls{Valid? vs}) (e:logS_entry) : option logK_entry =
  let st = thread_store vs in
  match e with
  | Get_S s k v -> 
      if store_contains st s && k = stored_key st s
      then Some (Spec.Get k v) else None
  | Put_S s k v -> 
      if store_contains st s && k = stored_key st s
      then Some (Spec.Put k v) else None
  | AddM_S _ r s' -> 
      if store_contains st s' && is_merkle_key (stored_key st s') 
      then Some (Spec.AddM r (stored_key st s')) else None
  | EvictM_S s s' -> 
      if store_contains st s && store_contains st s' && is_merkle_key (stored_key st s') 
      then Some (Spec.EvictM (stored_key st s) (stored_key st s')) else None
  | AddB_S _ r t j -> 
      Some (Spec.AddB r t j)
  | EvictB_S s t -> 
      if store_contains st s
      then Some (Spec.EvictB (stored_key st s) t) else None
  | EvictBM_S s s' t ->
      if store_contains st s && store_contains st s' && is_merkle_key (stored_key st s') 
      then Some (Spec.EvictBM (stored_key st s) (stored_key st s') t) else None

let lemma_t_verify_step_valid_implies_log_exists (vs:vtls) (e:logS_entry)
  : Lemma (requires (Valid? (t_verify_step vs e)))
          (ensures (Some? (logS_to_logK_entry vs e)))
          [SMTPat (Some? (logS_to_logK_entry vs e))]
  = ()

let rec lemma_t_verify_aux_valid_implies_log_exists (vs:vtls) (l:logS)
  : Lemma (requires (Valid? (fst (t_verify_aux vs l))))
          (ensures (Some? (snd (t_verify_aux vs l))))
          (decreases (Seq.length l))
  = let n = Seq.length l in
    if n <> 0 
    then lemma_t_verify_aux_valid_implies_log_exists vs (prefix l (n - 1))

let init_thread_state_valid (id:thread_id)
  : Lemma (Valid? (init_thread_state id))
  = ()

let lemma_empty_store_rel () 
  : Lemma (store_rel (empty_store store_size) Spec.empty_store)
  = lemma_as_map_empty store_size

let lemma_init_thread_state_rel (id:thread_id)
  : Lemma (vtls_rel (init_thread_state id) (Spec.init_thread_state id))
  = let vs = Valid id (empty_store store_size) (MkTimestamp 0 0) empty_hash_value empty_hash_value in 
    let vs' = Spec.Valid id Spec.empty_store (MkTimestamp 0 0) Root empty_hash_value empty_hash_value in
    lemma_empty_store_rel ();
    if id = 0 
    then 
      let st = thread_store vs in
      let st' = Spec.thread_store vs' in
      lemma_store_rel_add_to_store st st' 0 Root (init_value Root) Spec.MAdd

let lemma_t_verify_step_simulates_spec1 (vs:vtls) (vs':Spec.vtls) (e:logS_entry)
  : Lemma (requires (vtls_rel vs vs' /\ 
                     not (has_failed vs) /\ 
                     Valid? (t_verify_step vs e)))
          (ensures (vtls_rel (t_verify_step vs e) 
                             (Spec.t_verify_step vs' (Some?.v (logS_to_logK_entry vs e)))))
  = let st = thread_store vs in
    match e with
    | Get_S s k v -> lemma_vget_simulates_spec vs vs' s k v
    | Put_S s k v -> lemma_vput_simulates_spec vs vs' s k v
    | AddM_S s r s' -> lemma_vaddm_simulates_spec vs vs' s s' r (stored_key st s')
    | EvictM_S s s' -> lemma_vevictm_simulates_spec vs vs' s s' (stored_key st s) (stored_key st s')
    | AddB_S s r t j -> lemma_vaddb_simulates_spec vs vs' s r t j
    | EvictB_S s t -> lemma_vevictb_simulates_spec vs vs' s (stored_key st s) t
    | EvictBM_S s s' t -> lemma_vevictbm_simulates_spec vs vs' s s' (stored_key st s) (stored_key st s') t

let lemma_t_verify_step_simulates_spec2 (vs:vtls) (vs':Spec.vtls) (e:logS_entry)
  : Lemma (requires (vtls_rel vs vs' /\ has_failed vs))
          (ensures (forall (e':logK_entry). vtls_rel (t_verify_step vs e) (Spec.t_verify_step vs' e')))
  = if Valid? vs
    then
      match e with
      | Get_S s k v -> lemma_vget_has_failed vs s k v
      | Put_S s k v -> lemma_vput_has_failed vs s k v
      | AddM_S s r s' -> lemma_vaddm_has_failed vs s s' r
      | EvictM_S s s' -> lemma_vevictm_has_failed vs s s'
      | AddB_S s r t j -> lemma_vaddb_has_failed vs s r t j
      | EvictB_S s t -> lemma_vevictb_has_failed vs s t
      | EvictBM_S s s' t -> lemma_vevictbm_has_failed vs s s' t

let get_log (vs:vtls) (l:logS{Valid? (fst (t_verify_aux vs l))}) : logK
  = Some?.v (snd (t_verify_aux vs l))

let rec lemma_get_log_length (vs:vtls) (l:logS)
  : Lemma (requires (Valid? (fst (t_verify_aux vs l))))
          (ensures (Seq.length l = Seq.length (get_log vs l)))
          (decreases (Seq.length l))
          [SMTPat (Seq.length (get_log vs l))]
  = let n = Seq.length l in
    if n <> 0
    then
      let lp = prefix l (n - 1) in
      lemma_get_log_length vs lp

let lemma_get_log_prefix_commute (vs:vtls) (l:logS)
  : Lemma (requires (Valid? (fst (t_verify_aux vs l)) /\ Seq.length l > 0))
          (ensures (let n = Seq.length l in
                    Seq.equal (get_log vs (prefix l (n - 1))) (prefix (get_log vs l) (n - 1))))
  = ()

let rec lemma_t_verify_aux_simulates_spec (vs:vtls) (vs':Spec.vtls) (l:logS)
  : Lemma (requires (vtls_rel vs vs' /\ Valid? (fst (t_verify_aux vs l))))
          (ensures (let res = t_verify_aux vs l in
                    vtls_rel (fst res) (Spec.t_verify_aux vs' (Some?.v (snd res)))))
          (decreases (Seq.length l))
  = let n = Seq.length l in
    if n <> 0
    then
      let lp = prefix l (n - 1) in
      let e = Seq.index l (n - 1) in
      let (vsp,lp') = t_verify_aux vs lp in
      if Valid? vsp
      then (
        lemma_t_verify_aux_simulates_spec vs vs' lp; // I.H.
        let vsp' = Spec.t_verify_aux vs' (Some?.v lp') in
        lemma_get_log_prefix_commute vs l;
        if thread_store_is_map vsp
        then lemma_t_verify_step_simulates_spec1 vsp vsp' e
        else lemma_t_verify_step_simulates_spec2 vsp vsp' e
      )

let lemma_t_verify_simulates_spec (id:thread_id) (l:logS) 
  : Lemma (requires (Valid? (t_verify id l)))
          (ensures (vtls_rel (t_verify id l) (Spec.t_verify id (logS_to_logK id l))))
  = lemma_init_thread_state_rel id;
    lemma_t_verify_aux_simulates_spec (init_thread_state id) (Spec.init_thread_state id) l

let rec lemma_get_log_to_state_op (vs:vtls) (l:logS{Valid? (fst (t_verify_aux vs l))})
  : Lemma (ensures (Seq.equal (to_state_op_logS l) 
                              (Veritas.EAC.to_state_op_vlog (get_log vs l))))
          (decreases (Seq.length l))
  = let n = Seq.length l in
    if n = 0
    then (
      Seq.lemma_empty l;
      lemma_filter_empty is_state_op;
      lemma_filter_empty Veritas.EAC.is_state_op
    )
    else (
      let lp = prefix l (n - 1) in
      let e = Seq.index l (n - 1) in
      let (vsp,lp') = t_verify_aux vs lp in
      if Valid? vsp
      then (
        lemma_get_log_to_state_op vs lp; // I.H.
        lemma_get_log_prefix_commute vs l;        
        if is_state_op e
        then (
          lemma_filter_extend2 is_state_op l;
          lemma_filter_extend2 Veritas.EAC.is_state_op (get_log vs l);
          assert(Seq.equal (to_state_op_logS l) (append1 (to_state_op_logS lp) (to_state_op e)))
        )
        else (
          lemma_filter_extend1 is_state_op l;
          lemma_filter_extend1 Veritas.EAC.is_state_op (get_log vs l)
        )
      )
    )

let lemma_logS_to_logK_to_state_op (id:thread_id) (l:logS{Valid? (t_verify id l)})
  : Lemma (ensures (Seq.equal (to_state_op_logS l) 
                              (Veritas.EAC.to_state_op_vlog (logS_to_logK id l))))
  = lemma_get_log_to_state_op (init_thread_state id) l

(* Aggregate add and evict hashes over all verifier threads; follows the definition in 
   Veritas.Verifier.Global *)

let lemma_prefix_verifiable (gl: verifiable_log) (i:seq_index gl)
  : Lemma (ensures verifiable (prefix gl i))
          [SMTPat (verifiable (prefix gl i))]
  = let glp = prefix gl i in
    let aux (tid:seq_index glp)
      : Lemma (ensures (Valid? (verify (thread_log glp tid))))
      = assert(thread_log glp tid = thread_log gl tid) in
    Classical.forall_intro aux

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

let rec forall_is_map_aux (gl: verifiable_log) 
  : Tot bool (decreases (Seq.length gl))
  = let n = Seq.length gl in
    if n = 0 then true
    else
      let glp = prefix gl (n - 1) in
      thread_store_is_map (verify (thread_log gl (n - 1))) && forall_is_map_aux glp

let forall_is_map (gl:verifiable_log) : bool = forall_is_map_aux gl

let rec lemma_forall_is_map (gl:verifiable_log) (i:seq_index gl)
  : Lemma (requires (forall_is_map gl))
          (ensures (thread_store_is_map (verify (thread_log gl i))))
          (decreases (Seq.length gl))
  = let n = Seq.length gl in
    if n <> 0
    then
      let glp = prefix gl (n - 1) in
      if i < n - 1 then lemma_forall_is_map glp i

let lemma_verifiable_append1  (gl:SpecVG.verifiable_log) (l:logK{SpecVT.verifiable (Seq.length gl, l)})
  : Lemma (SpecVG.verifiable (append1 gl l))
  = let gl' = append1 gl l in
    assert (Seq.length gl' = Seq.length gl + 1);
    let aux (i:seq_index gl') : Lemma (SpecVT.verifiable (SpecVG.thread_log gl' i))
      = if i < Seq.length gl 
        then assert (SpecVT.verifiable (SpecVG.thread_log gl i)) in
    Classical.forall_intro aux

let rec glogS_to_logK_aux (gl: verifiable_log{forall_is_map gl}) 
  : Tot (gl':SpecVG.verifiable_log{Seq.length gl = Seq.length gl'})
    (decreases (Seq.length gl))
  = let n = Seq.length gl in
    if n = 0 then Seq.empty
    else (
      let glp = prefix gl (n - 1) in
      let e = Seq.index gl (n - 1) in
      lemma_t_verify_simulates_spec (n - 1) e;
      lemma_verifiable_append1 (glogS_to_logK_aux glp) (logS_to_logK (n - 1) e);
      append1 (glogS_to_logK_aux glp) (logS_to_logK (n - 1) e)
    )

let glogS_to_logK (gl:verifiable_log{forall_is_map gl}) : gl':SpecVG.verifiable_log{Seq.length gl = Seq.length gl'}
  = glogS_to_logK_aux gl

let rec lemma_glogS_to_logK_aux (gl:verifiable_log{forall_is_map gl}) (id:seq_index gl)
  : Lemma (ensures Seq.index (glogS_to_logK gl) id = logS_to_logK id (Seq.index gl id))
          (decreases (Seq.length gl))
  = let n = Seq.length gl in
    if n <> 0
    then if id < n - 1
    then let glp = prefix gl (n - 1) in
         lemma_glogS_to_logK_aux glp id

let lemma_glogS_to_logK (gl:verifiable_log{forall_is_map gl}) (id:seq_index gl)
  : Lemma (ensures Seq.index (glogS_to_logK gl) id = logS_to_logK id (Seq.index gl id))
  = lemma_glogS_to_logK_aux gl id

let hadd_values_equal (gl:verifiable_log{forall_is_map gl}) 
  : Lemma (hadd gl = SpecVG.hadd (glogS_to_logK gl))
  = admit()

let hevict_values_equal (gl:verifiable_log{forall_is_map gl}) 
  : Lemma (hevict gl = SpecVG.hevict (glogS_to_logK gl))
  = admit()
