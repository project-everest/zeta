module Veritas.Intermediate.VerifySKC

let vget (s:slot_id) (v:data_value) (vs: vtls {Valid? vs}) : vtls =
  let st = thread_store vs in
  (* check store contains slot s *)
  if not (store_contains st s) then Failed
  (* check stored key and value *)
  else let v' = stored_value st s in
       if not (DVal? v') then Failed
       else if to_data_value v' <> v then Failed
       else vs

let vput (s:slot_id) (v:data_value) (vs: vtls {Valid? vs}) : vtls =
  let st = thread_store vs in
  (* check store contains slot s *)
  if not (store_contains st s) then Failed
  (* check stored key is k *)
  else if not (is_data_key (stored_key st s)) then Failed
  else update_thread_store vs (update_store st s (DVal v))

let vaddm (s:slot_id) (r:record) (s':slot_id) (vs: vtls {Valid? vs}): vtls =
  let st = thread_store vs in
  let (k,v) = r in
  if not (s < Seq.length st.data) then Failed
  (* check store contains slot s' *)
  else if not (store_contains st s') then Failed
  else
    let k' = stored_key st s' in
    let v' = stored_value st s' in
    let a' = add_method_of st s' in
    (* check k is a proper desc of k' *)
    if not (is_proper_desc k k') then Failed
    (* check store does not contain slot s *)
    else if store_contains st s then Failed
    (* check store does not contain key k
       >> in lower levels we will check this via 'in_store' fields *)
    else if store_contains_key st k then Failed
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
  (* epoch of timestamp of last evict *)
  let e = MkTimestamp?.e t in
  let st = thread_store vs in 
  let (k,v) = r in
  if not (s < Seq.length st.data) then Failed
  else 
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
      (* check k is not in the store; update the valid flag accordingly *)
      let valid = not (store_contains_key st k) in
      let st_upd = {st with is_map=(st.is_map && valid)} in
      (* add record to store *)
      let st_upd2 = add_to_store st_upd s k v Spec.BAdd in
      update_thread_store vs_upd2 st_upd2

let vevictb (s:slot_id) (t:timestamp) (vs:vtls {Valid? vs}): vtls = 
  let clock = thread_clock vs in
  let e = MkTimestamp?.e t in
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

let lemma_store_contains (st:vstore) (st':Spec.vstore) (s:slot_id) (k:key)
  : Lemma (requires (store_rel st st' /\ slot_key_equiv st s k))
          (ensures (store_contains st s = Spec.store_contains st' k))
  = lemma_as_map_slot_key_equiv st s k

let lemma_stored_value (st:vstore) (st':Spec.vstore) (s:slot_id) (k:data_key)
  : Lemma (requires (store_rel st st' /\ slot_key_equiv st s k))
          (ensures (Spec.store_contains st' k /\ stored_value st s = Spec.stored_value st' k))
  = lemma_as_map_slot_key_equiv st s k

let lemma_update_store (st:vstore) (st':Spec.vstore) (s:slot_id) (k:data_key) (v:data_value)
  : Lemma (requires (store_rel st st' /\ slot_key_equiv st s k))
          (ensures (Spec.store_contains st' k /\
                    store_rel (update_store st s (DVal v)) (Spec.update_store st' k (DVal v))))
  = lemma_as_map_slot_key_equiv st s k;
    admit()

let lemma_vget_simulates_spec 
      (vs:vtls{Valid? vs})
      (vs':Spec.vtls{Spec.Valid? vs'})
      (s:slot_id)
      (k:data_key)
      (v:data_value)
  : Lemma (requires (vtls_rel vs vs' /\ slot_key_rel vs s k))
          (ensures (vtls_rel (vget s v vs) (Spec.vget k v vs')))
  = let st = thread_store vs in
    let st' = Spec.thread_store vs' in
    lemma_store_contains st st' s k;
    lemma_stored_value st st' s k

let lemma_vget_has_failed (vs:vtls{Valid? vs}) (s:slot_id) (v:data_value)
  : Lemma (requires (not (thread_store_is_map vs)))
          (ensures (has_failed (vget s v vs)))
  = admit()

let lemma_vput_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s:slot_id) 
      (k:data_key) 
      (v:data_value) 
  : Lemma (requires (vtls_rel vs vs' /\ slot_key_rel vs s k))
          (ensures (vtls_rel (vput s v vs) (Spec.vput k v vs'))) 
  = let st = thread_store vs in
    let st' = Spec.thread_store vs' in
    lemma_store_contains st st' s k;
    lemma_update_store st st' s k v

let lemma_vput_has_failed (vs:vtls{Valid? vs}) (s:slot_id) (v:data_value)
  : Lemma (requires (not (thread_store_is_map vs)))
          (ensures (has_failed (vput s v vs)))
  = admit()

let lemma_vaddm_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s s':slot_id)
      (r:record)
      (k':merkle_key)  
  : Lemma (requires (vtls_rel vs vs') /\ slot_key_rel vs s' k')
          (ensures (vtls_rel (vaddm s r s' vs) (Spec.vaddm r k' vs'))) 
  = let st = thread_store vs in
    let st' = Spec.thread_store vs' in
    let (k,v) = r in
    // ...
    admit()

let lemma_vaddm_has_failed (vs:vtls{Valid? vs}) (s s':slot_id) (r:record)
  : Lemma (requires (not (thread_store_is_map vs)))
          (ensures (has_failed (vaddm s r s' vs)))
  = admit()

let lemma_vevictm_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s s':slot_id)
      (k:key)
      (k':merkle_key)  
  : Lemma (requires (vtls_rel vs vs' /\ slot_key_rel vs s k /\ slot_key_rel vs s' k'))
          (ensures (vtls_rel (vevictm s s' vs) (Spec.vevictm k k' vs'))) 
  = admit()

let lemma_vevictm_has_failed (vs:vtls{Valid? vs}) (s s':slot_id)
  : Lemma (requires (not (thread_store_is_map vs)))
          (ensures (has_failed (vevictm s s' vs)))
  = admit()

let lemma_vaddb_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s:slot_id)
      (r:record)
      (t:timestamp)
      (j:thread_id)
  : Lemma (requires (vtls_rel vs vs'))
          (ensures (vtls_rel (vaddb s r t j vs) (Spec.vaddb r t j vs'))) 
  = admit()

let lemma_vaddb_has_failed (vs:vtls{Valid? vs}) (s:slot_id) (r:record) (t:timestamp) (j:thread_id)
  : Lemma (requires (not (thread_store_is_map vs)))
          (ensures (has_failed (vaddb s r t j vs)))
  = admit()

let lemma_vevictb_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s:slot_id)
      (k:key)
      (t:timestamp)
  : Lemma (requires (vtls_rel vs vs' /\ slot_key_rel vs s k))
          (ensures (vtls_rel (vevictb s t vs) (Spec.vevictb k t vs'))) 
  = admit()

let lemma_vevictb_has_failed (vs:vtls{Valid? vs}) (s:slot_id) (t:timestamp)
  : Lemma (requires (not (thread_store_is_map vs)))
          (ensures (has_failed (vevictb s t vs)))
  = admit()

let lemma_vevictbm_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s s':slot_id)
      (k:key)
      (k':merkle_key)
      (t:timestamp)
  : Lemma (requires (vtls_rel vs vs' /\ slot_key_rel vs s k /\ slot_key_rel vs s' k'))
          (ensures (vtls_rel (vevictbm s s' t vs) (Spec.vevictbm k k' t vs'))) 
  = admit()

let lemma_vevictbm_has_failed (vs:vtls{Valid? vs}) (s s':slot_id) (t:timestamp)
  : Lemma (requires (not (thread_store_is_map vs)))
          (ensures (has_failed (vevictbm s s' t vs)))
  = admit()

// TODO: what should the initial size be?
let store_size = 65536 // 2 ^ 16
let empty_store:vstore = { data=Seq.create store_size None; is_map=true }

(* Initialize verifier state *)
let init_thread_state (id:thread_id): vtls = 
  let vs = Valid id empty_store (MkTimestamp 0 0) empty_hash_value empty_hash_value in  
  if id = 0 then
    let st0 = thread_store vs in
    let st0_upd = add_to_store st0 0 Root (init_value Root) Spec.MAdd in
    update_thread_store vs st0_upd    
  else vs

let init_thread_state_valid (id:thread_id)
  : Lemma (Valid? (init_thread_state id))
  = admit()

let lemma_init_thread_state_rel (id:thread_id)
  : Lemma (vtls_rel (init_thread_state id) (Spec.init_thread_state id))
  = admit()

let lemma_t_verify_step_simulates_spec (vs:vtls) (vs':Spec.vtls) (e:logSK_entry) (e':logK_entry)
  : Lemma (requires (vtls_rel vs vs' /\ (has_failed vs \/ log_entry_rel vs e e')))
          (ensures (vtls_rel (t_verify_step vs e) (Spec.t_verify_step vs' e')))
  = if Valid? vs
    then if thread_store_is_map vs
    then
      match e, e' with
      | Get_SK s _ v, Spec.Get k v' -> 
          lemma_vget_simulates_spec vs vs' s k v
      | Put_SK s _ v, Spec.Put k v' ->  
          lemma_vput_simulates_spec vs vs' s k v
      | AddM_SK s r s' _, Spec.AddM r' k' ->  
          lemma_vaddm_simulates_spec vs vs' s s' r k'
      | EvictM_SK s _ s' _, Spec.EvictM k k' ->  
          lemma_vevictm_simulates_spec vs vs' s s' k k'
      | AddB_SK s r t j, Spec.AddB r' t' j' ->  
          lemma_vaddb_simulates_spec vs vs' s r t j
      | EvictB_SK s _ t, Spec.EvictB k t' ->  
          lemma_vevictb_simulates_spec vs vs' s k t
      | EvictBM_SK s _ s' _ t, Spec.EvictBM k k' t' ->  
          lemma_vevictbm_simulates_spec vs vs' s s' k k' t
    else
      match e with
      | Get_SK s _ v -> lemma_vget_has_failed vs s v
      | Put_SK s _ v -> lemma_vput_has_failed vs s v
      | AddM_SK s r s' _ -> lemma_vaddm_has_failed vs s s' r
      | EvictM_SK s _ s' _ -> lemma_vevictm_has_failed vs s s'
      | AddB_SK s r t j -> lemma_vaddb_has_failed vs s r t j
      | EvictB_SK s _ t -> lemma_vevictb_has_failed vs s t
      | EvictBM_SK s _ s' _ t -> lemma_vevictbm_has_failed vs s s' t

let rec lemma_t_verify_aux_simulates_spec (vs:vtls) (vs':Spec.vtls) (l:logSK) (l':logK)
  : Lemma (requires (vtls_rel vs vs' /\ Seq.length l = Seq.length l' /\ (Valid? vs ==> log_rel_with_vtls vs l l')))
          (ensures (vtls_rel (t_verify_aux vs l) (Spec.t_verify_aux vs' l')))
          (decreases (Seq.length l))
  = let n = Seq.length l in
    if n <> 0
    then
      (* intermediate repr. *)
      let l2 = prefix l (n - 1) in
      let vs2 = t_verify_aux vs l2 in
      let e = Seq.index l (n - 1) in
      (* spec repr. *)
      let l2' = prefix l' (n - 1) in
      let vs2' = Spec.t_verify_aux vs' l2' in
      let e' = Seq.index l' (n - 1) in
      if Valid? vs 
      then (
        lemma_t_verify_aux_simulates_spec vs vs' l2 l2';
        lemma_t_verify_step_simulates_spec vs2 vs2' e e' 
      )
      else admit() // in this case, both results are Failed

let lemma_t_verify_simulates_spec (id:thread_id) (l:logSK) (l':logK)
  : Lemma (requires (log_rel l l'))
          (ensures (vtls_rel (t_verify id l) (Spec.t_verify id l')))
  = lemma_init_thread_state_rel id;
    lemma_log_rel l l';
    lemma_t_verify_aux_simulates_spec (init_thread_state id) (Spec.init_thread_state id) l l'
