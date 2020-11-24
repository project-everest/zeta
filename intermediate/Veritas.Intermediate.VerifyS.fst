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

let lemma_update_value_preserves_key_with_MAdd
  (st:vstore)
  (s:slot_id{store_contains st s}) 
  (v:value_type_of (stored_key st s))
  (k:key)
  : Lemma (ensures store_contains_key_with_MAdd st k = store_contains_key_with_MAdd (update_value st s v) k)
          [SMTPat (store_contains_key_with_MAdd (update_value st s v) k)]
  = admit()

let lemma_update_value_DVal_preserves_merkle_inv (st:vstore) (s:slot_id{store_contains st s /\ is_data_key (stored_key st s)}) (v:data_value)
  : Lemma (requires merkle_store_inv st)
          (ensures merkle_store_inv (update_value st s (DVal v)))
          [SMTPat (merkle_store_inv (update_value st s (DVal v)))]
  = let st' = update_value st s (DVal v) in
    let aux1 (s':slot_id{store_contains st' s' /\ MVal? (stored_value st' s')})
      : Lemma (in_store_flag_unset_equals_desc_not_in_store st' s')
      = assert (in_store_flag_unset_equals_desc_not_in_store st s') in
    let aux2 (s':slot_id{store_contains st' s' /\ MVal? (stored_value st' s')})
      : Lemma (points_to_nearest_desc_in_store st' s')
      = assert (points_to_nearest_desc_in_store st s') in
    Classical.forall_intro aux1;
    Classical.forall_intro aux2

let lemma_vput_simulates_SC
      (vs:vtls{Valid? vs}) 
      (vs':SC.vtls{SC.Valid? vs'}) 
      (s:slot_id) 
      (k:data_key) 
      (v:data_value) 
  : Lemma (requires (vtls_rel vs vs'))
          (ensures (vtls_rel (vput s k v vs) (SC.vput s k v vs'))) 
  = ()





let lemma_add_to_store_preserves_key_with_MAdd (st:vstore) (s:st_index st{not (store_contains st s)}) (k:key) (v:value_type_of k) (k0:key)
  : Lemma (requires k <> k0)
          (ensures store_contains_key_with_MAdd st k0 = store_contains_key_with_MAdd (add_to_store st s k v Spec.MAdd) k0)
          [SMTPat (store_contains_key_with_MAdd (add_to_store st s k v Spec.MAdd) k0)]
  = admit()

let lemma_add_to_store_adds_key_with_MAdd (st:vstore) (s:st_index st{not (store_contains st s)}) (k:key) (v:value_type_of k)
  : Lemma (ensures store_contains_key_with_MAdd (add_to_store st s k v Spec.MAdd) k)
          [SMTPat (store_contains_key_with_MAdd (add_to_store st s k v Spec.MAdd) k)]
  = admit()

let lemma_update_in_store_preserves_key_with_MAdd (st:vstore) (s:slot_id{store_contains st s}) (d:bin_tree_dir) (b:bool) (k:key)
  : Lemma (ensures store_contains_key_with_MAdd st k = store_contains_key_with_MAdd (update_in_store st s d b) k)
          [SMTPat (store_contains_key_with_MAdd (update_in_store st s d b) k)]
  = admit()




let lemma_addm_case1 (st:vstore) (s:st_index st) (s':slot_id{store_contains st s'}) (k:key)
  : Lemma (requires (let k' = stored_key st s' in
                     let v' = stored_value st s' in
                     not (store_contains st s) /\
                     MVal? v' /\ 
                     is_proper_desc k k' /\
                     Empty? (desc_hash_dir (to_merkle_value v') (desc_dir k k')) /\
                     merkle_store_inv st))
          (ensures (let v' = to_merkle_value (stored_value st s') in
                    let d = desc_dir k (stored_key st s') in
                    let h = hashfn (init_value k) in
                    let v'_upd = Spec.update_merkle_value v' d k h false in
                    let st_upd = update_value st s' (MVal v'_upd) in
                    let st_upd2 = add_to_store st_upd s k (init_value k) Spec.MAdd in
                    let st_upd3 = update_in_store st_upd2 s' d true in
                    merkle_store_inv st_upd3))
  = let k' = stored_key st s' in
    let v' = to_merkle_value (stored_value st s') in
    let d = desc_dir k (stored_key st s') in
    let h = hashfn (init_value k) in
    let v'_upd = Spec.update_merkle_value v' d k h false in
    let st_upd = update_value st s' (MVal v'_upd) in
    let st_upd2 = add_to_store st_upd s k (init_value k) Spec.MAdd in
    let st_upd3 = update_in_store st_upd2 s' d true in
    let aux1 (s0:slot_id{store_contains st_upd3 s0 /\ MVal? (stored_value st_upd3 s0)})
      : Lemma (in_store_flag_unset_equals_desc_not_in_store st_upd3 s0)
      = if s0 <> s
        then (
          assert (in_store_flag_unset_equals_desc_not_in_store st s0);
          if s0 <> s'
          then (
            assert (points_to_nearest_desc_in_store st s0);
            // points_to_nearest_desc_in_store implies the assumptions below, right?
            let v0 = to_merkle_value (stored_value st s0) in
            let dhl = desc_hash_dir v0 Left in
            if Desc? dhl then assume (Desc?.k dhl <> k);
            let dhr = desc_hash_dir v0 Right in
            if Desc? dhr then assume (Desc?.k dhr <> k)
          )
        ) in
    let aux2 (s0:slot_id{store_contains st_upd3 s0 /\ MVal? (stored_value st_upd3 s0)})
      : Lemma (points_to_nearest_desc_in_store st_upd3 s0)
      = if s0 = s 
        then (
          assert (points_to_nearest_desc_in_store st s');
          let aux2_inner (k0:key{is_proper_desc k0 k})
            : Lemma (not (store_contains_key_with_MAdd st_upd3 k0))
            = lemma_proper_desc_transitive1 k0 k k';
              lemma_two_related_desc_same_dir k0 k k' in
          Classical.forall_intro aux2_inner
        )
        else (
          assert (points_to_nearest_desc_in_store st s0);
          if s0 = s'
          then admit()
          else admit()
        ) in 
    Classical.forall_intro aux1;
    Classical.forall_intro aux2


// The hard part here is showing that each case preserves merkle_store_inv
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
              // CASE 1 - k' has no descendent hash in direction d
              assert (points_to_nearest_desc_in_store st s');
              assert (not (store_contains_key_with_MAdd st k));
              lemma_addm_case1 st s s' k
          | Desc k2 h2 b2 -> 
              if k2 = k 
              // CASE 2 - k' has a descendent hash for k, and its in_store flag is not set           
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
              // CASE 3 - k' has a descendent hash for k2, and k is between k' and k2
              else (
                assert (points_to_nearest_desc_in_store st s');              
                if v = init_value k && is_proper_desc k2 k 
                then (
                  assert (not (store_contains_key_with_MAdd st k));
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
              )
#pop-options



let lemma_evict_from_store_preserves_key_with_MAdd (st:vstore) (s:slot_id{store_contains st s}) (k:key)
  : Lemma (requires stored_key st s <> k)
          (ensures store_contains_key_with_MAdd st k = store_contains_key_with_MAdd (evict_from_store st s) k)
          [SMTPat (store_contains_key_with_MAdd (evict_from_store st s) k)]
  = admit()

let lemma_evictm_case1
  (st:vstore)
  (s:slot_id{store_contains st s}) 
  (s':slot_id{store_contains st s'})
  : Lemma (requires merkle_store_inv st /\ is_proper_desc (stored_key st s) (stored_key st s'))
          (ensures (let d = desc_dir (stored_key st s) (stored_key st s') in
                    let st_upd = evict_from_store st s in
                    let st_upd2 = update_in_store st_upd s' d false in
                    merkle_store_inv st_upd2))
  = let d = desc_dir (stored_key st s) (stored_key st s') in
    let st_upd = evict_from_store st s in
    let st_upd2 = update_in_store st_upd s' d false in
    let aux1 (s0:slot_id{store_contains st_upd2 s0 /\ MVal? (stored_value st_upd2 s0)})
      : Lemma (in_store_flag_unset_equals_desc_not_in_store st_upd2 s0)
      = assert (in_store_flag_unset_equals_desc_not_in_store st s0);
        let v0 = to_merkle_value (stored_value st s0) in
        let dhl = desc_hash_dir v0 Left in
        let dhr = desc_hash_dir v0 Right in
        if s0 <> s' 
        then (
          assert (stored_value st s0 = stored_value st_upd s0);
          assert (stored_value st_upd s0 = stored_value st_upd2 s0);
          assert (stored_key st s0 = stored_key st_upd2 s0);
          if Desc? dhl
          then (
            assert (child_in_store st s0 Left = child_in_store st_upd2 s0 Left);
            assume (Desc?.k dhl <> stored_key st s);
            assert (store_contains_key_with_MAdd st (Desc?.k dhl) = store_contains_key_with_MAdd st_upd (Desc?.k dhl))
          )
        );
        //else (
        //  if Desc? dhl
        //  then assert (child_in_store
        //  admit()
        //) 
        admit() in
    let aux2 (s0:slot_id{store_contains st_upd2 s0 /\ MVal? (stored_value st_upd2 s0)})
      : Lemma (points_to_nearest_desc_in_store st_upd2 s0)
      = admit() in //assert (points_to_nearest_desc_in_store st s') in
    Classical.forall_intro aux1;
    Classical.forall_intro aux2





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
  = let mv = to_merkle_value (stored_value st s) in
    let Desc k _ _ = desc_hash_dir mv d in
    let mv' = Spec.update_merkle_value mv d k h b in
    let st' = update_value st s (MVal mv') in
    let aux1 (s':slot_id{store_contains st' s' /\ MVal? (stored_value st' s')})
      : Lemma (in_store_flag_unset_equals_desc_not_in_store st' s')
      = assert (in_store_flag_unset_equals_desc_not_in_store st s') in
    let aux2 (s':slot_id{store_contains st' s' /\ MVal? (stored_value st' s')})
      : Lemma (points_to_nearest_desc_in_store st' s')
      = assert (points_to_nearest_desc_in_store st s') in
    Classical.forall_intro aux1;
    Classical.forall_intro aux2

let lemma_vevictm_simulates_SC 
      (vs:vtls{Valid? vs}) 
      (vs':SC.vtls{SC.Valid? vs'}) 
      (s s':slot_id)  
  : Lemma (requires (vtls_rel vs vs'))
          (ensures (vtls_rel (vevictm s s' vs) (SC.vevictm s s' vs'))) 
  = let st = thread_store vs in
    if store_contains st s && store_contains st s'
    then 
      let k = stored_key st s in
      let v = stored_value st s in
      let k' = stored_key st s' in
      let v' = stored_value st s' in
      if is_proper_desc k k' && not (has_instore_merkle_desc st s)
      then
        let d = desc_dir k k' in
        let _ = assert (is_value_of k' v') in 
        let v' = to_merkle_value v' in
        let dh' = desc_hash_dir v' d in
        let h = hashfn v in
        match dh' with
        | Empty -> ()
        | Desc k2 h2 b2 -> 
          if k2 = k 
          then
            let st_upd = update_hash_and_blum_bit st s' d h false in
            let st_upd2 = evict_from_store st_upd s in
            let st_upd3 = update_in_store st_upd2 s' d false in
            assert (merkle_store_inv st_upd);
            lemma_evictm st_upd s s'


let lemma_add_to_store_BAdd_preserves_key_with_MAdd (st:vstore) (s:st_index st{not (store_contains st s)}) (k:key) (v:value_type_of k) (k0:key)
  : Lemma (ensures store_contains_key_with_MAdd st k0 = store_contains_key_with_MAdd (add_to_store st s k v Spec.BAdd) k0)
          [SMTPat (store_contains_key_with_MAdd (add_to_store st s k v Spec.BAdd) k0)]
  = admit()


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


let lemma_evict_from_store_preserves_inv (st:vstore) (s:slot_id{store_contains st s})
  : Lemma (requires merkle_store_inv st /\ add_method_of st s = Spec.BAdd)
          (ensures merkle_store_inv (evict_from_store st s))
          [SMTPat (merkle_store_inv (evict_from_store st s))]
  = admit()

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
