module Veritas.Intermediate.VerifyS

(* Relation between a slot and key *)

let slot_key_rel (vs: vtls {Valid? vs}) (s:slot_id) (k:key) =
  let st = thread_store vs in slot_key_equiv st s k

(* Simulation lemmas for v* functions *)

let lemma_vget_simulates_spec 
      (vs:vtls{Valid? vs})
      (vs':Spec.vtls{Spec.Valid? vs'})
      (s:slot_id)
      (k:data_key)
      (v:data_value)
  : Lemma (requires (vtls_rel vs vs' /\ 
                     slot_key_rel vs s k))
          (ensures (vtls_rel (vget s k v vs) (Spec.vget k v vs')))
  = ()

let lemma_vget_preserves_inv
      (vs:vtls{Valid? vs})
      (s:slot_id)
      (k:data_key)
      (v:data_value)
  : Lemma (requires (Valid? (vget s k v vs) /\
                     store_inv (thread_store vs)))
          (ensures (store_inv (thread_store (vget s k v vs))))
  = ()

let lemma_vput_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s:slot_id) 
      (k:data_key) 
      (v:data_value) 
  : Lemma (requires (vtls_rel vs vs' /\
                     slot_key_rel vs s k))
          (ensures (vtls_rel (vput s k v vs) (Spec.vput k v vs'))) 
  = ()

(* updating a data value preserves in_store_inv *)
let lemma_update_value_DVal_preserves_in_store_inv 
      (st:vstore) 
      (s:slot_id{store_contains st s /\ is_data_key (stored_key st s)}) 
      (v:data_value)
  : Lemma (requires in_store_inv st)
          (ensures in_store_inv (update_value st s (DVal v)))
  = let st_upd = update_value st s (DVal v) in
    let aux (s0:instore_merkle_slot st_upd) (d0:bin_tree_dir{points_to_some st_upd s0 d0})
      : Lemma (let k = pointed_key st_upd s0 d0 in
               in_store_bit st_upd s0 d0 = store_contains_key_with_MAdd st_upd k)
      = let k0 = pointed_key st s0 d0 in
        assert (in_store_bit st s0 d0 = store_contains_key_with_MAdd st k0) in
    Classical.forall_intro_2 aux

let lemma_vput_preserves_inv
      (vs:vtls{Valid? vs}) 
      (s:slot_id) 
      (k:data_key) 
      (v:data_value) 
  : Lemma (requires (Valid? (vput s k v vs) /\
                     store_inv (thread_store vs)))
          (ensures (store_inv (thread_store (vput s k v vs)))) 
  = lemma_update_value_DVal_preserves_in_store_inv (thread_store vs) s v

// TODO: flaky
#push-options "--z3rlimit_factor 2"
let lemma_vaddm_simulates_spec_if_k_is_new
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s s':slot_id)
      (r:record)
      (k':merkle_key)  
   : Lemma (requires (s < thread_store_size vs /\
                      not (store_contains (thread_store vs) s) /\
                      not (store_contains_key (thread_store vs) (fst r)) /\ // key is new
                      vtls_rel vs vs' /\ 
                      slot_key_rel vs s' k' /\
                      store_inv (thread_store vs)))
           (ensures (vtls_rel (vaddm s r s' vs) (Spec.vaddm r k' vs'))) 
  = ()
#pop-options

(* st satisfies store_inv everywhere except for slot s, direction d 
   --> this is helpful in the vaddm and vevictm proofs because it allows us to
       say that the invariant is partially-satisfied in the middle of a step
*)
let store_inv_except (st:vstore) (s:instore_merkle_slot st) (d:bin_tree_dir)
  = is_map st /\
    (forall (s0:instore_merkle_slot st) 
       (d0:bin_tree_dir{points_to_some st s0 d0 /\ ~ (s = s0 /\ d = d0)}).
         let k0 = pointed_key st s0 d0 in
         in_store_bit st s0 d0 = store_contains_key_with_MAdd st k0)

(* updating a merkle value to point to a new key preserves the invariant *)
let lemma_update_merkle_value_to_point_to_new_key_preserves_inv
      (st:vstore)
      (s:instore_merkle_slot st)
      (k:key{not (store_contains_key_with_MAdd st k)})
      (d:bin_tree_dir)
      (h:ms_hash_value)
      (b:bool)
  : Lemma (requires (store_inv st))
          (ensures (let v = to_merkle_value (stored_value st s) in
                    let v_upd = Spec.update_merkle_value v d k h b in
                    let st_upd = update_value st s (MVal v_upd) in  
                    store_inv_except st_upd s d))
  = let v = to_merkle_value (stored_value st s) in
    let v_upd = Spec.update_merkle_value v d k h b in
    let st_upd = update_value st s (MVal v_upd) in
    let aux (s0:instore_merkle_slot st_upd) 
            (d0:bin_tree_dir{points_to_some st_upd s0 d0 /\ ~ (s0 = s /\ d0 = d)}) 
      : Lemma (let k0 = pointed_key st_upd s0 d0 in
               in_store_bit st_upd s0 d0 = store_contains_key_with_MAdd st_upd k0)
      = let k0 = pointed_key st s0 d0 in
        assert (in_store_bit st s0 d0 = store_contains_key_with_MAdd st k0) in
    Classical.forall_intro_2 aux

(* some useful properties that follow from EAC
   
   NOTE: we could also prove other_dir_does_not_point_to using properties
   of the intermediate-level functions, but I don't think we can maintain the
   no_other_slot_points_to constraint *)
let no_other_slot_points_to (st:vstore) (s:instore_merkle_slot st) (k:key)
  = forall (s':instore_merkle_slot st{s <> s'}) (d:bin_tree_dir{points_to_some st s' d}). 
      pointed_key st s' d <> k

let other_dir_does_not_point_to (st:vstore) (s:instore_merkle_slot st) (d:bin_tree_dir) (k:key)
  = not (points_to_some st s (other_dir d)) || 
    pointed_key st s (other_dir d) <> k

(* when adding a new (k,v) pair, we need to satisfy a few properties
   to preserve in_store_inv. In particular: 
   * v cannot point to anything in the store via a merkle add
   * v cannot point to k *)
let valid_new_value (st:vstore) (k:key) (v:value_type_of k)
  = MVal? v ==>
    (let mv = to_merkle_value v in
     forall (d:bin_tree_dir{mv_points_to_some mv d}).
       let pk = mv_pointed_key mv d in
       not (store_contains_key_with_MAdd st pk) && pk <> k) 

(* adding a slot requires updating the in_store bit *)
let lemma_add_to_store_update_in_store_preserves_inv1
      (st:vstore)
      (s':instore_merkle_slot st)
      (s:st_index st{not (store_contains st s)})
      (d:bin_tree_dir{points_to_some st s' d})
      (k:key{not (store_contains_key st k)})
      (v:value_type_of k)
  : Lemma (requires (store_inv_except st s' d /\
                     pointed_key st s' d = k /\
                     no_other_slot_points_to st s' k /\
                     other_dir_does_not_point_to st s' d k /\
                     valid_new_value st k v))
          (ensures (let st_upd = add_to_store st s k v Spec.MAdd in
                    let st_upd2 = update_in_store st_upd s' d true in
                    store_inv st_upd2))
  = let st_upd = add_to_store st s k v Spec.MAdd in
    let st_upd2 = update_in_store st_upd s' d true in
    let aux (s0:instore_merkle_slot st_upd2) (d0:bin_tree_dir{points_to_some st_upd2 s0 d0})
      : Lemma (let k0 = pointed_key st_upd2 s0 d0 in
               in_store_bit st_upd2 s0 d0 = store_contains_key_with_MAdd st_upd2 k0)
      = if s0 = s' && d0 = d
        then () // follows from the call to update_in_store
        else if s0 = s
        then () // follows from the constraints on v
        else 
          let k0 = pointed_key st s0 d0 in
          assert (in_store_bit st s0 d0 = store_contains_key_with_MAdd st k0) // follows from store_inv st
      in
    Classical.forall_intro_2 aux

(* modified form of the lemma above used in the third case of vaddm; 
   the lemma above assumes that the added value (v) does not point to anything
   currently in the store, while this lemma assumes that v points to key vk
   in direction vd, which may or may not be in the store (dictated by vd). *)
let lemma_add_to_store_update_in_store_preserves_inv2
      (st:vstore)
      (s':instore_merkle_slot st)
      (s:st_index st{not (store_contains st s)})
      (d:bin_tree_dir{points_to_some st s' d})
      (k:merkle_key{not (store_contains_key st k)})
      (v:merkle_value)
      (vk:key{k <> vk})
      (vd:bin_tree_dir{mv_points_to_some v vd})
      (vb:bool{vb = store_contains_key_with_MAdd st vk})
  : Lemma (requires (store_inv_except st s' d /\
                     pointed_key st s' d = k /\
                     no_other_slot_points_to st s' k /\
                     other_dir_does_not_point_to st s' d k /\
                     Empty? (desc_hash_dir v (other_dir vd)) /\
                     mv_pointed_key v vd = vk))
          (ensures (let st_upd = add_to_store st s k (MVal v) Spec.MAdd in
                    let st_upd2 = update_in_store st_upd s' d true in
                    let st_upd3 = update_in_store st_upd2 s vd vb in
                    store_inv st_upd3))
  = let st_upd = add_to_store st s k (MVal v) Spec.MAdd in
    let st_upd2 = update_in_store st_upd s' d true in
    let st_upd3 = update_in_store st_upd2 s vd vb in
    let aux (s0:instore_merkle_slot st_upd3) (d0:bin_tree_dir{points_to_some st_upd3 s0 d0})
      : Lemma (let k0 = pointed_key st_upd3 s0 d0 in
               in_store_bit st_upd3 s0 d0 = store_contains_key_with_MAdd st_upd3 k0)
      = if s0 = s
        then ()
        else if s0 = s' && d0 = d
        then ()
        else let k0 = pointed_key st s0 d0 in
          assert (in_store_bit st s0 d0 = store_contains_key_with_MAdd st k0) in
    Classical.forall_intro_2 aux

let lemma_update_value_no_other_slot_points_to
      (st:vstore)
      (s:instore_merkle_slot st)
      (k:key)
      (v:value_type_of (stored_key st s))
  : Lemma (requires (no_other_slot_points_to st s k))
          (ensures (no_other_slot_points_to (update_value st s v) s k))
          [SMTPat (no_other_slot_points_to (update_value st s v) s k)]
  = let st_upd = update_value st s v in
    let aux (s0:instore_merkle_slot st_upd{s0 <> s}) (d0:bin_tree_dir{points_to_some st_upd s0 d0})
      : Lemma (pointed_key st_upd s0 d0 <> k)
      = assert (pointed_key st s0 d0 <> k) in
    Classical.forall_intro_2 aux

let lemma_update_in_store_no_other_slot_points_to
      (st:vstore)
      (s:instore_merkle_slot st)
      (k:key)
      (d:bin_tree_dir)
      (b:bool)
  : Lemma (requires (no_other_slot_points_to st s k))
          (ensures (no_other_slot_points_to (update_in_store st s d b) s k))
          [SMTPat (no_other_slot_points_to (update_in_store st s d b) s k)]
  = let st_upd = update_in_store st s d b in
    let aux (s0:instore_merkle_slot st_upd{s0 <> s}) (d0:bin_tree_dir{points_to_some st_upd s0 d0})
      : Lemma (pointed_key st_upd s0 d0 <> k)
      = assert (pointed_key st s0 d0 <> k) in
    Classical.forall_intro_2 aux

let lemma_vaddm_preserves_inv_if_k_is_new
      (vs:vtls{Valid? vs}) 
      (s s':slot_id)
      (r:record)
   : Lemma (requires (Valid? (vaddm s r s' vs) /\
                      (let st = thread_store vs in
                       let k' = stored_key st s' in
                       let (k,v) = r in
                       let d = desc_dir k k' in
                       store_inv st /\
                       // properties below come from EAC
                       ~ (store_contains_key st k) /\ // key is new
                       no_other_slot_points_to st s' k /\ // no slot besides s' points to k
                       other_dir_does_not_point_to st s' d k /\ // s' only points to k in one dir
                       valid_new_value st k v)))
           (ensures (store_inv (thread_store (vaddm s r s' vs)))) 
  = let st = thread_store vs in
    let (k,v) = r in
    let k' = stored_key st s' in
    let v' = to_merkle_value (stored_value st s') in
    let d = desc_dir k k' in
    let dh' = desc_hash_dir v' d in 
    let h = hashfn v in
    match dh' with
    | Empty ->
        let v'_upd = Spec.update_merkle_value v' d k h false in
        let st_upd = update_value st s' (MVal v'_upd) in
        lemma_update_merkle_value_to_point_to_new_key_preserves_inv st s' k d h false;
        lemma_add_to_store_update_in_store_preserves_inv1 st_upd s' s d k v
    | Desc k2 h2 b2 ->
        if k2 = k 
        then lemma_add_to_store_update_in_store_preserves_inv1 st s' s d k v
        else ( 
          let d2 = desc_dir k2 k in
          let inb = in_store_bit st s' d in
          let v_upd = Spec.update_merkle_value (to_merkle_value v) d2 k2 h2 b2 in
          let v'_upd = Spec.update_merkle_value v' d k h false in
          let st_upd = update_value st s' (MVal v'_upd) in
          lemma_update_merkle_value_to_point_to_new_key_preserves_inv st s' k d h false;
          lemma_add_to_store_update_in_store_preserves_inv2 st_upd s' s d k v_upd k2 d2 inb
        )

let lemma_has_instore_merkle_desc (st:vstore) (st':Spec.vstore) (s:slot_id) (k:key)
  : Lemma (requires (store_inv st /\ store_rel st st' /\ slot_key_equiv st s k))
          (ensures (has_instore_merkle_desc st s = Spec.has_instore_merkle_desc st' k))
          [SMTPat (has_instore_merkle_desc st s); SMTPat (Spec.has_instore_merkle_desc st' k)]
  = ()

let lemma_vevictm_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s s':slot_id)
      (k:key)
      (k':merkle_key)  
  : Lemma (requires (vtls_rel vs vs' /\ 
                     slot_key_rel vs s k /\ 
                     slot_key_rel vs s' k' /\
                     store_inv (thread_store vs)))
          (ensures (vtls_rel (vevictm s s' vs) (Spec.vevictm k k' vs'))) 
  = ()

(* updating a merkle value preserves the invariant if you leave the pointed-to key the same *)
let lemma_update_merkle_value_with_same_key_preserves_inv
      (st:vstore)
      (s:instore_merkle_slot st)
      (k:key)
      (d:bin_tree_dir{points_to_some st s d})
      (h:ms_hash_value)
      (b:bool)
  : Lemma (requires (store_inv st /\
                     pointed_key st s d = k))
          (ensures (let v = to_merkle_value (stored_value st s) in
                    let v_upd = Spec.update_merkle_value v d k h b in
                    store_inv (update_value st s (MVal v_upd))))
  = let v = to_merkle_value (stored_value st s) in
    let v_upd = Spec.update_merkle_value v d k h b in
    let st_upd = update_value st s (MVal v_upd) in
    let aux (s0:instore_merkle_slot st_upd) (d0:bin_tree_dir{points_to_some st_upd s0 d0})
      : Lemma (let k0 = pointed_key st_upd s0 d0 in
               in_store_bit st_upd s0 d0 = store_contains_key_with_MAdd st_upd k0)
      = let k0 = pointed_key st s0 d0 in
        assert(in_store_bit st s0 d0 = store_contains_key_with_MAdd st k0) in
    Classical.forall_intro_2 aux

(* evicting a slot requires updating the in_store bit *)
let lemma_evict_from_store_update_in_store_preserves_inv
      (st:vstore)
      (s':instore_merkle_slot st)
      (s:slot_id{store_contains st s /\ s <> s'})
      (d:bin_tree_dir{points_to_some st s' d})
  : Lemma (requires (let k = stored_key st s in
                     store_inv st /\
                     pointed_key st s' d = k /\
                     no_other_slot_points_to st s' k /\
                     other_dir_does_not_point_to st s' d k))
          (ensures (let st_upd = evict_from_store st s in
                    store_inv (update_in_store st_upd s' d false)))
  = let st_upd = evict_from_store st s in
    let st_upd2 = update_in_store st_upd s' d false in
    let aux (s0:instore_merkle_slot st_upd2) (d0:bin_tree_dir{points_to_some st_upd s0 d0})
      : Lemma (let k0 = pointed_key st_upd2 s0 d0 in
               in_store_bit st_upd2 s0 d0 = store_contains_key_with_MAdd st_upd2 k0)
      = assert (s0 <> s); // not possible that s0 = s because s is not in the store
        let k0 = pointed_key st_upd2 s0 d0 in
        if s0 = s' && d0 = d
        then (
          assert (not (in_store_bit st_upd2 s0 d0));
          assert (not (store_contains_key_with_MAdd st_upd2 k0))
        ) 
        else if s0 = s' 
        then (
          assert (k0 <> stored_key st s); // by points_to_unique
          assert (in_store_bit st s0 d0 = store_contains_key_with_MAdd st k0)
        ) 
        else (
          assert (pointed_key st s0 d0 <> (stored_key st s)); // by points_to_unique
          assert (k0 <> stored_key st s);
          assert (in_store_bit st s0 d0 = store_contains_key_with_MAdd st k0)
        ) in
    Classical.forall_intro_2 aux

let lemma_vevictm_preserves_inv 
      (vs:vtls{Valid? vs}) 
      (s s':slot_id)
  : Lemma (requires (Valid? (vevictm s s' vs) /\
                     (let st = thread_store vs in 
                      let k = stored_key st s in
                      let k' = stored_key st s' in
                      let d = desc_dir k k' in
                      store_inv st /\
                      pointed_key st s' d = k /\
                      no_other_slot_points_to st s' k /\
                      other_dir_does_not_point_to st s' d k)))
                     (ensures (store_inv (thread_store (vevictm s s' vs)))) 
  = let st = thread_store vs in
    let k = stored_key st s in
    let v = stored_value st s in
    let k' = stored_key st s' in
    let v' = stored_value st s' in
    let d = desc_dir k k' in
    let v' = to_merkle_value v' in
    let dh' = desc_hash_dir v' d in
    let h = hashfn v in
    match dh' with
    | Desc k2 h2 b2 ->
        let v'_upd = Spec.update_merkle_value v' d k h false in
        let st_upd = update_value st s' (MVal v'_upd) in
        lemma_update_merkle_value_with_same_key_preserves_inv st s' k d h false;
        lemma_evict_from_store_update_in_store_preserves_inv st_upd s' s d

let lemma_vaddb_simulates_spec_if_k_is_new 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s:slot_id)
      (r:record)
      (t:timestamp)
      (j:thread_id)
  : Lemma (requires (s < thread_store_size vs /\ 
                     not (store_contains (thread_store vs) s) /\ 
                     not (store_contains_key (thread_store vs) (fst r)) /\ // key is new
                     vtls_rel vs vs'))
          (ensures (vtls_rel (vaddb s r t j vs) (Spec.vaddb r t j vs')))
  = ()

let lemma_add_to_store_BAdd_preserves_inv
      (st:vstore)
      (s:st_index st{not (store_contains st s)})
      (k:key{not (store_contains_key st k)})
      (v:value_type_of k)
  : Lemma (requires (store_inv st /\
                     valid_new_value st k v))
          (ensures (let st_upd = add_to_store st s k v Spec.BAdd in
                    store_inv st_upd))
  = let st_upd = add_to_store st s k v Spec.BAdd in
    let aux (s0:instore_merkle_slot st_upd) (d0:bin_tree_dir{points_to_some st_upd s0 d0})
      : Lemma (let k0 = pointed_key st_upd s0 d0 in
               in_store_bit st_upd s0 d0 = store_contains_key_with_MAdd st_upd k0)
      = if s0 = s
        then () // follows from the constraints on v
        else 
          let k0 = pointed_key st s0 d0 in
          assert (in_store_bit st s0 d0 = store_contains_key_with_MAdd st k0) // follows from store_inv st
      in
    Classical.forall_intro_2 aux

let lemma_vaddb_preserves_inv_if_k_is_new 
      (vs:vtls{Valid? vs}) 
      (s:slot_id)
      (r:record)
      (t:timestamp)
      (j:thread_id)
  : Lemma (requires (Valid? (vaddb s r t j vs) /\
                     (let st = thread_store vs in
                      let (k,v) = r in
                      store_inv st /\
                      not (store_contains_key st k) /\
                      valid_new_value st k v)))
          (ensures (store_inv (thread_store (vaddb s r t j vs))))
  = lemma_add_to_store_BAdd_preserves_inv (thread_store vs) s (fst r) (snd r)

let lemma_vevictb_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s:slot_id)
      (k:key)
      (t:timestamp)
  : Lemma (requires (store_inv (thread_store vs) /\ 
                     vtls_rel vs vs' /\ 
                     slot_key_rel vs s k))
          (ensures (vtls_rel (vevictb s t vs) (Spec.vevictb k t vs'))) 
  = ()

(* evicting a blum slot preserves in_store_inv *)
let lemma_evict_from_store_BAdd_preserves_inv
      (st:vstore)
      (s:slot_id{store_contains st s})
  : Lemma (requires (store_inv st /\ add_method_of st s = Spec.BAdd))
          (ensures (store_inv (evict_from_store st s)))
  = let st_upd = evict_from_store st s in
    let aux (s0:instore_merkle_slot st_upd) (d0:bin_tree_dir{points_to_some st_upd s0 d0})
      : Lemma (let k = pointed_key st_upd s0 d0 in
               in_store_bit st_upd s0 d0 = store_contains_key_with_MAdd st_upd k)
      = assert (s0 <> s); 
        let k0 = pointed_key st s0 d0 in
        assert (in_store_bit st s0 d0 = store_contains_key_with_MAdd st k0) in
    Classical.forall_intro_2 aux

let lemma_vevictb_preserves_inv 
      (vs:vtls{Valid? vs}) 
      (s:slot_id)
      (t:timestamp)
  : Lemma (requires (store_inv (thread_store vs) /\
                     Valid? (vevictb s t vs)))
          (ensures (store_inv (thread_store (vevictb s t vs))))
  = lemma_evict_from_store_BAdd_preserves_inv (thread_store vs) s

let lemma_vevictbm_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s s':slot_id)
      (k:key)
      (k':merkle_key)
      (t:timestamp)
  : Lemma (requires (vtls_rel vs vs' /\ slot_key_rel vs s k /\ slot_key_rel vs s' k'))
          (ensures (vtls_rel (vevictbm s s' t vs) (Spec.vevictbm k k' t vs'))) 
  = () // TODO: suspicious -- why does the unit proof work?

let lemma_vevictbm_preserves_inv 
      (vs:vtls{Valid? vs}) 
      (s s':slot_id)
      (t:timestamp)
  : Lemma (requires (store_inv (thread_store vs) /\ Valid? (vevictbm s s' t vs)))
          (ensures (store_inv (thread_store (vevictbm s s' t vs))))
  = () // TODO: VERY suspicious

(* This is basically a "light" version of the vfun functions to reconstruct the log. 
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

(*
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
*)
let lemma_t_verify_simulates_spec (id:thread_id) (l:logS) 
  : Lemma (requires (Valid? (t_verify id l)))
          (ensures (vtls_rel (t_verify id l) (Spec.t_verify id (logS_to_logK id l))))
  = admit()
    //lemma_init_thread_state_rel id;
    //lemma_t_verify_aux_simulates_spec (init_thread_state id) (Spec.init_thread_state id) l

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

let lemma_tl_verifiable_implies_prefix_verifiable
  (tl:tl_verifiable_log) (i:nat{i <= tl_length tl}):
  Lemma (ensures (tl_verifiable (tl_prefix tl i)))
  = admit()

let lemma_gl_verifiable_implies_prefix_verifiable
  (gl:gl_verifiable_log) (i:nat{i <= Seq.length gl}):
  Lemma (ensures (gl_verifiable (prefix gl i)))
  = let glp = prefix gl i in
    let aux (tid:seq_index glp)
      : Lemma (ensures (Valid? (verify (thread_log glp tid))))
      = assert(thread_log glp tid = thread_log gl tid) in
    Classical.forall_intro aux

let lemma_verifiable_append1  (gl:SpecVG.verifiable_log) (l:logK{SpecVT.verifiable (Seq.length gl, l)})
  : Lemma (SpecVG.verifiable (append1 gl l))
  = let gl' = append1 gl l in
    assert (Seq.length gl' = Seq.length gl + 1);
    let aux (i:seq_index gl') : Lemma (SpecVT.verifiable (SpecVG.thread_log gl' i))
      = if i < Seq.length gl 
        then assert (SpecVT.verifiable (SpecVG.thread_log gl i)) in
    Classical.forall_intro aux

let rec glogS_to_logK_aux (gl:gl_verifiable_log{forall_is_map gl}) 
  : Tot (gl':SpecVG.verifiable_log{Seq.length gl = Seq.length gl'})
    (decreases (Seq.length gl))
  = let n = Seq.length gl in
    if n = 0 then Seq.empty
    else (
      let glp = prefix gl (n - 1) in
      let e = Seq.index gl (n - 1) in
      admit()
      //lemma_t_verify_simulates_spec (n - 1) e;
      //lemma_verifiable_append1 (glogS_to_logK_aux glp) (logS_to_logK (n - 1) e);
      //append1 (glogS_to_logK_aux glp) (logS_to_logK (n - 1) e)
    )

let glogS_to_logK (gl:gl_verifiable_log{forall_is_map gl}) 
  : gl':SpecVG.verifiable_log{Seq.length gl = Seq.length gl'}
  = glogS_to_logK_aux gl

let rec lemma_glogS_to_logK_aux (gl:gl_verifiable_log{forall_is_map gl}) (id:seq_index gl)
  : Lemma (ensures Seq.index (glogS_to_logK gl) id = logS_to_logK id (Seq.index gl id))
          (decreases (Seq.length gl))
  = admit()
    //let n = Seq.length gl in
    //if n <> 0
    //then if id < n - 1
    //then let glp = prefix gl (n - 1) in
    //     lemma_glogS_to_logK_aux glp id

let lemma_glogS_to_logK (gl:gl_verifiable_log{forall_is_map gl}) (id:seq_index gl)
  : Lemma (ensures Seq.index (glogS_to_logK gl) id = logS_to_logK id (Seq.index gl id))
  = lemma_glogS_to_logK_aux gl id

(*
let lemma_prefix_verifiable_and_forall_is_map (gl:gl_verifiable_log{forall_is_map gl}) (i:seq_index gl)
  : Lemma (ensures gl_verifiable (prefix gl i) /\ forall_is_map (prefix gl i))
          [SMTPat (gl_verifiable (prefix gl i))]
  = let glp = prefix gl i in
    let aux1 (tid:seq_index glp)
      : Lemma (Valid? (verify (thread_log glp tid)))
      = assert(thread_log glp tid = thread_log gl tid) in
    Classical.forall_intro aux1;
    let aux2 (tid:seq_index glp)
      : Lemma (thread_store_is_map (verify (thread_log glp tid)))
      = assert(thread_log glp tid = thread_log gl tid) in
    Classical.forall_intro aux2

let lemma_prefix_glogS_to_logK_comm (gl:verifiable_log{forall_is_map gl}) (i:seq_index gl)
  : Lemma (ensures Seq.equal (prefix (glogS_to_logK gl) i) (glogS_to_logK (prefix gl i)))
          [SMTPat (prefix (glogS_to_logK gl) i)]
  = ()
*)

let rec hadd_equal_aux (gl:gl_verifiable_log{forall_is_map gl}) 
  : Lemma (ensures hadd gl = SpecVG.hadd (glogS_to_logK gl))
          (decreases (Seq.length gl))
  = let n = Seq.length gl in
    if n <> 0
    then ( 
      let glp = prefix gl (n - 1) in
      admit()
      //hadd_values_equal_aux glp;
      //lemma_t_verify_simulates_spec (n - 1) (Seq.index gl (n - 1))
    )

let lemma_hadd_equal (gl:gl_verifiable_log{forall_is_map gl}) 
  : Lemma (hadd gl = SpecVG.hadd (glogS_to_logK gl))
  = hadd_equal_aux gl

let rec hevict_equal_aux (gl:gl_verifiable_log{forall_is_map gl}) 
  : Lemma (ensures hevict gl = SpecVG.hevict (glogS_to_logK gl))
          (decreases (Seq.length gl))
  = let n = Seq.length gl in
    if n <> 0
    then ( 
      let glp = prefix gl (n - 1) in
      admit()
      //hevict_values_equal_aux glp;
      //lemma_t_verify_simulates_spec (n - 1) (Seq.index gl (n - 1))
    )

let lemma_hevict_equal (gl:gl_verifiable_log{forall_is_map gl}) 
  : Lemma (hevict gl = SpecVG.hevict (glogS_to_logK gl))
  = hevict_equal_aux gl

let clock_sorted (il: il_logS {il_verifiable il})
  = admit()
 
let lemma_prefix_verifiable (itsl: its_log) (i:nat{i <= I.length itsl}):
  Lemma (ensures (il_verifiable (I.prefix itsl i) /\ clock_sorted (I.prefix itsl i)))
  = admit()

let il_create (gl: gl_verifiable_log): (itsl:its_log{g_logS_of itsl == gl})
  = admit()




(*************************************)



let thread_state (itsl:its_log)
                 (tid:valid_tid itsl)
  : Tot (vs:vtls{Valid? vs})
  = verify (thread_log (I.s_seq itsl) tid)

let il_thread_id_of (itsl: its_log) (i: I.seq_index itsl): valid_tid itsl =
  fst (I.i2s_map itsl i)

let thread_state_pre (itsl: its_log) (i: I.seq_index itsl): (vs:vtls{Valid? vs}) = 
  let tid = il_thread_id_of itsl i in
  thread_state (I.prefix itsl i) tid

let thread_state_post (itsl: its_log) (i: I.seq_index itsl): (vs:vtls{Valid? vs}) = 
  let tid = il_thread_id_of itsl i in
  thread_state (I.prefix itsl (i + 1)) tid

let lemma_verifier_thread_state_extend (itsl: its_log) (i: I.seq_index itsl):
  Lemma (thread_state_post itsl i == 
         t_verify_step (thread_state_pre itsl i) (I.index itsl i))
  = admit()

let forall_store_inv (itsl:its_log)
  = forall (tid:valid_tid itsl). store_inv (thread_store (thread_state itsl tid))
  
let forall_vtls_rel (itsl:its_log) (itsl':SpecVTS.its_log) 
  = thread_count itsl = SpecVTS.thread_count itsl' /\
    (forall (tid:valid_tid itsl). 
       vtls_rel (thread_state itsl tid) 
                (SpecVTS.thread_state itsl' tid))

let ilogS_to_logK (il:its_log{forall_store_inv il}) : SpecVTS.its_log
  = admit()

// WANT: I.index (ilogS_to_logK itsl) i == 
//       logS_to_logK_entry (thread_state_pre itsl i) (I.index itsl i) 

let lemma_ilogS_to_logK_length (itsl:its_log{forall_store_inv itsl})
  : Lemma (ensures I.length itsl = I.length (ilogS_to_logK itsl))
          [SMTPat (I.length (ilogS_to_logK itsl))]
  = admit()

let lemma_ilogS_to_logK_thread_count (itsl:its_log{forall_store_inv itsl})
  : Lemma (ensures thread_count itsl = SpecVTS.thread_count (ilogS_to_logK itsl))
          [SMTPat (SpecVTS.thread_count (ilogS_to_logK itsl))]
  = admit()

// Also want a function that can take an il:its_log{forall_store_inv il} and an
// entry e such that adding e produces a state where is_map=true, but may or may
// not satisfy store_inv, and produces a SpecVTS.its_log
// --> still need to figure out exactly how this relates to ilogS_to_logK
let extend_spec_log 
      (il:its_log{forall_store_inv il}) 
      (tid:valid_tid il)
      (e:logS_entry{let vs = t_verify_step (thread_state il tid) e in
                    Valid? vs /\ is_map (thread_store vs)})
  : SpecVTS.its_log
  = admit()

let lemma_forall_store_inv_specialize (itsl:its_log) (i:I.seq_index itsl)
  : Lemma (requires (forall_store_inv (I.prefix itsl i)))
          (ensures (let tid = il_thread_id_of itsl i in
                    store_inv (thread_store (thread_state (I.prefix itsl i) tid))))
  = ()

let lemma_forall_store_inv_extend (itsl:its_log) (i:I.seq_index itsl)
  : Lemma (requires (let tid = il_thread_id_of itsl i in
                     forall_store_inv (I.prefix itsl i) /\ 
                     store_inv (thread_store (thread_state (I.prefix itsl (i + 1)) tid))))
          (ensures (forall_store_inv (I.prefix itsl (i + 1))))
  = admit()

//let lemma_forall_store_inv_prefix (itsl:its_log{forall_store_inv itsl}) (i:I.seq_index itsl)
//  : Lemma (ensures (forall_store_inv (I.prefix itsl i)))
//          [SMTPat (forall_store_inv (I.prefix itsl i))]
//  = admit()

let lemma_forall_vtls_rel_specialize (itsl:its_log) (i:I.seq_index itsl)
  : Lemma (requires (forall_store_inv (I.prefix itsl i) /\ 
                     forall_vtls_rel (I.prefix itsl i) (ilogS_to_logK (I.prefix itsl i))))
          (ensures (let tid = il_thread_id_of itsl i in
                    vtls_rel (thread_state (I.prefix itsl i) tid)
                             (SpecVTS.thread_state (ilogS_to_logK (I.prefix itsl i)) tid)))
  = admit()

let lemma_forall_vtls_rel_extend (itsl:its_log) (i:I.seq_index itsl)
  : Lemma (requires (let tid = il_thread_id_of itsl i in
                     let itsl_i = I.prefix itsl i in
                     forall_store_inv itsl_i /\
                     forall_vtls_rel itsl_i (ilogS_to_logK itsl_i) /\
                     (let e = I.index itsl i in
                      let vs = thread_state itsl_i tid in
                      let vs1 = t_verify_step vs e in
                       Valid? vs1 /\ is_map (thread_store vs1) /\
                       vtls_rel vs1 (SpecVTS.thread_state (extend_spec_log itsl_i tid e) tid))))
          (ensures (let tid = il_thread_id_of itsl i in
                    let e = I.index itsl i in
                    forall_vtls_rel (I.prefix itsl (i + 1)) (extend_spec_log (I.prefix itsl i) tid e)))
  = admit()

let test (itsl:its_log) (i:I.seq_index itsl)
  : Lemma 
    (requires 
      (let tid = il_thread_id_of itsl i in
       let itsl_i = I.prefix itsl i in
       forall_store_inv itsl_i /\
       forall_vtls_rel itsl_i (ilogS_to_logK itsl_i) /\
       store_inv (thread_store (thread_state (I.prefix itsl (i + 1)) tid)) /\
       (let e = I.index itsl i in
        let vs = thread_state itsl_i tid in
        let vs1 = t_verify_step vs e in
        Valid? vs1 /\
        is_map (thread_store vs1) /\
        vtls_rel vs1 (SpecVTS.thread_state (extend_spec_log itsl_i tid e) tid))))
    (ensures False)
  = let e = I.index itsl i in
    let tid = il_thread_id_of itsl i in
    let itsl_i = I.prefix itsl i in
    let itsl_k_i = ilogS_to_logK itsl_i in
    let vs' = SpecVTS.thread_state itsl_k_i tid in 
    let vs = thread_state itsl_i tid in
    let st = thread_store vs in
    match e with
    | AddM_S s (k,v) s' ->
      assume (not (store_contains_key st k));
      let k' = stored_key st s' in

      lemma_vaddm_simulates_spec_if_k_is_new vs vs' s s' (k,v) k';
      lemma_forall_store_inv_extend itsl i;
      lemma_forall_vtls_rel_extend itsl i;
      assert(false) // BAD - there must be a contradiction somewhere
    | _ -> admit()
                       

(* property that:
 *    (a) the intermediate verifiers all satisfy the store invariant
 *    (b) the spec level log is evict-add-consistent 
 *    (c) the intermediate and spec level verifiers states correspond to one-another (related)
 *)
let store_inv_spec_eac_rel (itsl: its_log) =
  forall_store_inv itsl /\
  (let itsl_k = ilogS_to_logK itsl in
   SpecVTS.is_eac itsl_k /\
   forall_vtls_rel itsl itsl_k)

(* a union type that contains a hash collision or a proof of store_inv_spec_eac_rel for a specific itsl log *)
let store_inv_spec_rel_or_hashcollision (itsl:its_log) = 
  o:option Veritas.Verifier.EAC.hash_collision_gen{Some? o \/ store_inv_spec_eac_rel itsl}

let inductive_step (itsl: il_hash_verifiable_log) 
                   (i:I.seq_index itsl {let itsl_i = I.prefix itsl i in
                                        store_inv_spec_eac_rel itsl_i}):
  store_inv_spec_rel_or_hashcollision (I.prefix itsl (i + 1)) =   

  let tid = il_thread_id_of itsl i in
  let itsl_i = I.prefix itsl i in
  let itsl_k_i = ilogS_to_logK itsl_i in
  let itsl_i1 = I.prefix itsl (i + 1) in

  // assert (SpecVTS.is_eac itsl_k_i);
  // assert (forall_store_inv itsl_i);
  // assert (forall_vtls_rel itsl_i itsl_k_i);

  let vs = thread_state itsl_i tid in
  let vs' = SpecVTS.thread_state itsl_k_i tid in 

  lemma_forall_store_inv_specialize itsl i;
  // assert (store_inv (thread_store vs));
  lemma_forall_vtls_rel_specialize itsl i;
  // assert (vtls_rel vs vs');

  lemma_verifier_thread_state_extend itsl i;
  //assert (thread_state_post itsl i == t_verify_step (thread_state_pre itsl i) (I.index itsl i));

  let st = thread_store vs in
  let e = I.index itsl i in
  match e with
  
  | Get_S s k v ->
    lemma_vget_simulates_spec vs vs' s k v;

    let itsl_k_i1 = extend_spec_log itsl_i tid e in
    if SpecVTS.is_eac itsl_k_i1 then (
       lemma_vget_preserves_inv vs s k v;
       lemma_forall_store_inv_extend itsl i;
       lemma_forall_vtls_rel_extend itsl i;
       None
    )
    else 
      Some (Veritas.Verifier.EAC.lemma_non_eac_get_implies_hash_collision itsl_k_i1)

  | Put_S s k v ->
    lemma_vput_simulates_spec vs vs' s k v;

    let itsl_k_i1 = extend_spec_log itsl_i tid e in
    if SpecVTS.is_eac itsl_k_i1 then (
       lemma_vput_preserves_inv vs s k v; 
       lemma_forall_store_inv_extend itsl i;        
       SpecVTS.lemma_verifier_thread_state_extend itsl_k_i1 i; 
       lemma_forall_vtls_rel_extend itsl i;
       None
    )
    else 
      Some (Veritas.Verifier.EAC.lemma_non_eac_put_implies_hash_collision itsl_k_i1)

  | AddM_S s (k,v) s' ->
      if store_contains_key st k
      then (
        // We know that the log up to this point is EAC and the verifier state satisfies store_inv.
        // Based on this, we should be able to show that it is impossible for the vaddm
        // to successfully verify the current entry (contradicting our assumption that itsl is a 
        // hash verifiable log).
        // --> if k is in the store via MAdd, then the in_store bit must be set by store_inv
        // --> if k is in the store via BAdd, then the evicted_to_blum bit must be set by EAC
        admit()
      )
      else (
        let k' = stored_key st s' in
        lemma_vaddm_simulates_spec_if_k_is_new vs vs' s s' (k,v) k';
        
        let itsl_k_i1 = extend_spec_log itsl_i tid e in
        if SpecVTS.is_eac itsl_k_i1 then (
          
          // The following should hold from eac -- right?
          assume(no_other_slot_points_to st s' k);
          assume(other_dir_does_not_point_to st s' (desc_dir k k') k);
          assume(valid_new_value st k v);

          lemma_vaddm_preserves_inv_if_k_is_new vs s s' (k,v); 
          lemma_forall_store_inv_extend itsl i;        
          lemma_forall_vtls_rel_extend itsl i;
          assert(false); // BAD - there must be a contradiction somewhere
          None
        )
        else 
          Some (Veritas.Verifier.EAC.lemma_non_eac_addm_implies_hash_collision itsl_k_i1)      
      )

  (*
    | EvictM_S s s' -> 
    | AddB_S s (k,v) t j ->
    | EvictB_S s t -> 
    | EvictBM_S s s' t -> 
  *)

  | _ -> 
    admit()

(* empty log satisfies all invariants *)
let lemma_empty_store_inv_spec_rel (itsl: its_log):
  Lemma (requires (I.length itsl = 0))
        (ensures (store_inv_spec_eac_rel itsl)) = admit()

let rec lemma_il_hash_verifiable_implies_eac_and_vtls_rel_aux 
      (itsl:il_hash_verifiable_log) 
      (i:nat{i <= I.length itsl}) 
  : Tot (store_inv_spec_rel_or_hashcollision (I.prefix itsl i))
    (decreases i)                 
  = let itsl_i = I.prefix itsl i in     
    if i = 0 then (
      lemma_empty_store_inv_spec_rel itsl_i;
      None
    )
    else 
      let hc_or_inv = lemma_il_hash_verifiable_implies_eac_and_vtls_rel_aux itsl (i - 1) in

      (* we found a hash collision - simply return the same *)
      if Some? hc_or_inv then
        Some (Some?.v hc_or_inv)
      else 
        // assert(store_inv_spec_rel_or_hashcollision itsl_i');
        inductive_step itsl (i - 1)      
    
let lemma_il_hash_verifiable_implies_eac_and_vtls_rel (itsl: il_hash_verifiable_log)
  : store_inv_spec_rel_or_hashcollision itsl     
  = I.lemma_fullprefix_equal itsl;
    lemma_il_hash_verifiable_implies_eac_and_vtls_rel_aux itsl (I.length itsl)

let lemma_store_inv_spec_eac_rel_implies_spec_hash_verifiable (itsl:il_hash_verifiable_log)
  : Lemma (requires store_inv_spec_eac_rel itsl)
          (ensures SpecVTS.hash_verifiable (ilogS_to_logK itsl))
  = admit()

let lemma_ilogS_to_logK_state_ops (il:its_log{forall_store_inv il})
  : Lemma (state_ops il == SpecVTS.state_ops (ilogS_to_logK il))
  = admit()

let lemma_time_seq_rw_consistent  
  (itsl: il_hash_verifiable_log {~ (Veritas.State.rw_consistent (state_ops itsl))})
  : Veritas.Verifier.EAC.hash_collision_gen = 
  let tsl = I.i_seq itsl in  
  let ts_ops = to_state_op_logS tsl in

  let hc_or_inv = lemma_il_hash_verifiable_implies_eac_and_vtls_rel itsl in

  (* if hc_or_inv returns a hash collision, then we can return the same collision *)
  if Some? hc_or_inv
  then Some?.v hc_or_inv

  (* otherwise, we can use the spec-level lemma *)
  else (
    assert (store_inv_spec_eac_rel itsl);
    
    let itsl_k = ilogS_to_logK itsl in

    lemma_store_inv_spec_eac_rel_implies_spec_hash_verifiable itsl;
    assert (SpecVTS.hash_verifiable itsl_k);

    lemma_ilogS_to_logK_state_ops itsl;
    assert (state_ops itsl == SpecVTS.state_ops itsl_k);

    Veritas.Verifier.Correctness.lemma_time_seq_rw_consistent itsl_k
  )

let lemma_logS_interleave_implies_state_ops_interleave (l: logS) (gl: g_logS{I.interleave #logS_entry l gl})
  : Lemma (I.interleave #Veritas.State.state_op (to_state_op_logS l) (to_state_op_glogS gl)) 
  = admit()

(* final correctness lemma; essentially a copy-and-paste from Veritas.Verifier.Correctness *)
let lemma_verifier_correct (gl: gl_hash_verifiable_log { ~ (Veritas.State.seq_consistent (to_state_op_glogS gl))})
  : Veritas.Verifier.EAC.hash_collision_gen 
  = (* sequences of per-thread put/get operations *)
    let g_ops = to_state_op_glogS gl in

    (* sequence ordered by time of each log entry *)
    let itsl = il_create gl in  
    I.lemma_interleaving_correct itsl;
    assert(I.interleave (I.i_seq itsl) gl);

    (* sequence of state ops induced by tmsl *)
    let ts_ops = state_ops itsl in

    lemma_logS_interleave_implies_state_ops_interleave (I.i_seq itsl) gl;
    assert(I.interleave ts_ops g_ops);

    (* if ts_ops is read-write consistent then we have a contradiction *)
    let is_rw_consistent = Veritas.SeqMachine.valid_all_comp Veritas.StateSeqMachine.ssm ts_ops in
    Veritas.StateSeqMachine.lemma_state_sm_equiv_rw_consistent ts_ops;

    if is_rw_consistent then (
      assert(Veritas.SeqMachine.valid_all Veritas.StateSeqMachine.ssm ts_ops);
      assert(Veritas.State.rw_consistent ts_ops);

      (* a contradiction *)
      assert(Veritas.State.seq_consistent g_ops);

      (* any return value *)
      Veritas.Verifier.EAC.SingleHashCollision (Collision (DVal Null) (DVal Null))
    )
    else  
      lemma_time_seq_rw_consistent itsl

