module Veritas.Intermediate.VerifyS

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

let lemma_init_thread_state_rel (id:thread_id)
  : Lemma (vtls_rel (init_thread_state id) (SC.init_thread_state id))
  = admit()

let lemma_t_verify_simulates_SC (id:thread_id) (l:logS) 
  : Lemma (vtls_rel (t_verify id l) (SC.t_verify id l))
  = admit()

let lemma_prefix_verifiable (gl: verifiable_log) (i:seq_index gl)
  : Lemma (ensures verifiable (prefix gl i))
  = admit()

let hadd_values_equal (gl:verifiable_log) : Lemma (hadd gl = SC.hadd gl)
  = admit()

let hevict_values_equal (gl:verifiable_log) : Lemma (hevict gl = SC.hevict gl)
  = admit()
