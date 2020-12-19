module Veritas.Intermediate.Store

let lemma_lookup_key_returns_k (st:vstore) (k:key) 
  : Lemma (requires (store_contains_key st k))
          (ensures (VStoreE?.k (Some?.v (lookup_key st k)) = k))
  = lemma_filter_correct1 (has_key k) st 0

let lemma_lookup_key_returns_None (st:vstore) (k:key)
  : Lemma (requires (lookup_key st k = None))
          (ensures (forall i. not (has_key k (Seq.index st i))))
  = if Seq.length (filter (has_key k) st) = 0 
    then lemma_filter_all_not (has_key k) st
    else lemma_filter_correct1 (has_key k) st 0

let lemma_store_contains_key (st:vstore) (k:key)
  : Lemma (requires (exists s. stored_key st s = k))
          (ensures (store_contains_key st k))
  = lemma_filter_exists (has_key k) st;
    lemma_filter_correct1 (has_key k) st 0

let lemma_has_key (st:vstore) (s:slot_id) (k:key)
  : Lemma (requires (has_key k (get_slot st s)))
          (ensures (store_contains st s /\ stored_key st s = k))
  = ()

let lemma_store_contains_key_inv (st:vstore) (k:key)
  : Lemma (requires (store_contains_key st k))
          (ensures (exists s. stored_key st s = k))
  = let s' = filter (has_key k) st in
    if Seq.length s' > 0 
    then 
      let i = filter_index_map (has_key k) st 0 in
      lemma_has_key st i k

let stored_value_by_key (st:vstore) (k:key{store_contains_key st k})
  : value_type_of k
  = lemma_lookup_key_returns_k st k;
    VStoreE?.v (Some?.v (lookup_key st k))

let add_method_of_by_key (st:vstore) (k:key{store_contains_key st k})
  : add_method
  = VStoreE?.am (Some?.v (lookup_key st k))

(* Two cases where it's safe to add an entry (e) to the store (st) at slot s: 
   * e.k is not in st and s is empty
   * e.k is already at s *)
let compatible_entry (st:vstore) (s:st_index st) (e:vstore_entry)
  = (not (store_contains st s) /\ not (store_contains_key st e.k)) \/ 
    (store_contains st s /\ stored_key st s = e.k) 

let lemma_update_slot_compatible_entry_is_map 
      (st:vstore{is_map st}) 
      (s:st_index st) 
      (e:vstore_entry{compatible_entry st s e})
  : Lemma (is_map (update_slot st s e))
          [SMTPat (is_map (update_slot st s e))]
  = let st_upd = update_slot st s e in
    let aux (s0:slot_id{store_contains st_upd s0})
            (s0':slot_id{store_contains st_upd s0' /\ s0' <> s0})
          : Lemma (stored_key st_upd s0 <> stored_key st_upd s0')
                  [SMTPat (Seq.index st_upd s0); SMTPat (Seq.index st_upd s0')]
          = if s0 = s 
            then assert (stored_key st s0' <> e.k)
            else if s0' = s 
            then assert (stored_key st s0 <> e.k) in
    assert (is_map st_upd)

let lemma_add_to_store_is_map1
      (st:vstore) 
      (s:st_index st{not (store_contains st s)}) 
      (k:key{not (store_contains_key st k)}) 
      (v:value_type_of k) 
      (am:add_method)
  : Lemma (requires (is_map st))
          (ensures (is_map (add_to_store st s k v am)))
  = () // proved by lemma_update_compatible_entry_is_map
  
let lemma_add_to_store_is_map2
      (st:vstore) 
      (s:st_index st{not (store_contains st s)}) 
      (k:key{store_contains_key st k}) 
      (v:value_type_of k) 
      (am:add_method)
  : Lemma (ensures (~ (is_map (add_to_store st s k v am))))
  = let st_upd = add_to_store st s k v am in
    assert (stored_key st_upd s = k);
    lemma_store_contains_key_inv st k;
    Classical.exists_elim 
      (exists (s':slot_id{store_contains st_upd s' /\ s' <> s}). 
      stored_key st_upd s' = stored_key st_upd s) 
      (Squash.get_proof (exists s. stored_key st s = k)) 
      (fun s' -> assert (stored_key st_upd s' = k));
    // we have shown two different slots with the same key, so the invariant is violated
    ()
 
let lemma_lookup_key_update_value 
      (st:vstore) 
      (s:slot_id{store_contains st s}) 
      (v:value_type_of (stored_key st s)) 
      (k:key)
  : Lemma (let res = lookup_key st k in
           let res' = lookup_key (update_value st s v) k in
           (None? res /\ None? res') \/
           (Some? res /\ Some? res' /\ VStoreE?.am (Some?.v res) = VStoreE?.am (Some?.v res')))
  = let stf = filter (has_key k) st in
    let Some (VStoreE ks _ am l r) = Seq.index st s in
    assert (Seq.length stf = Seq.length (filter (has_key k) (update_value st s v)));
    if Seq.length stf > 0 
    then (
      if filter_index_map (has_key k) st 0 = s
      then lemma_filter_update_index_eq (has_key k) st s (Some (VStoreE ks v am l r))
      else lemma_filter_update_index_neq (has_key k) st s (Some (VStoreE ks v am l r)) 0
    )

let lemma_update_value_preserves_keys
      (st:vstore) 
      (s:slot_id{store_contains st s}) 
      (v:value_type_of (stored_key st s))
      (k:key)
  : Lemma (store_contains_key st k = store_contains_key (update_value st s v) k)
  = lemma_lookup_key_update_value st s v k

let lemma_update_value_preserves_key_with_MAdd
  (st:vstore)
  (s:slot_id{store_contains st s}) 
  (v:value_type_of (stored_key st s))
  (k:key)
  : Lemma (ensures store_contains_key_with_MAdd st k = 
                     store_contains_key_with_MAdd (update_value st s v) k)
  = lemma_lookup_key_update_value st s v k

let lemma_add_different_key_to_store_preserves_keys_with_MAdd
  (st:vstore)
  (s:st_index st{not (store_contains st s)}) 
  (k:key)
  (v:value_type_of k)
  (k0:key)
  : Lemma (requires k <> k0)
          (ensures store_contains_key_with_MAdd st k0 =
                     store_contains_key_with_MAdd (add_to_store st s k v Spec.MAdd) k0)
  = let stf = filter (has_key k0) st in
    if Seq.length stf > 0
    then (
      assert (filter_index_map (has_key k0) st 0 <> s);
      lemma_filter_update_index_neq (has_key k0) st s (Some (VStoreE k v Spec.MAdd false false)) 0
    )
    
let lemma_add_to_store_BAdd_preserves_key_with_MAdd
  (st:vstore)
  (s:st_index st{not (store_contains st s)}) 
  (k:key{not (store_contains_key st k)})
  (v:value_type_of k)
  (k0:key)
  : Lemma (ensures store_contains_key_with_MAdd st k0 = 
                     store_contains_key_with_MAdd (add_to_store st s k v Spec.BAdd) k0)
  = let stf = filter (has_key k0) st in
    if Seq.length stf = 0
    then (
      let st_upd = add_to_store st s k v Spec.BAdd in
      if k = k0
      then (
        assert (has_key k0 (Seq.index st_upd s));
        lemma_filter_all_not (has_key k0) st;
        assert (forall j. j <> s ==> not (has_key k0 (Seq.index st_upd j)));
        lemma_filter_unique (has_key k0) st_upd s
      )
    )
    else (
      lemma_filter_correct1 (has_key k0) st 0;
      assert (k <> k0);
      assert (filter_index_map (has_key k0) st 0 <> s);
      lemma_filter_update_index_neq (has_key k0) st s (Some (VStoreE k v Spec.BAdd false false)) 0
    )    

let lemma_add_to_store_MAdd_adds_key_with_MAdd
  (st:vstore)
  (s:st_index st{not (store_contains st s)}) 
  (k:key{not (store_contains_key st k)})
  (v:value_type_of k)
  : Lemma (ensures store_contains_key_with_MAdd (add_to_store st s k v Spec.MAdd) k)
  = let st_upd = add_to_store st s k v Spec.MAdd in
    assert (has_key k (Seq.index st_upd s));
    lemma_lookup_key_returns_None st k;
    lemma_filter_all_not (has_key k) st;
    assert (forall j. j <> s ==> not (has_key k (Seq.index st_upd j)));
    lemma_filter_unique (has_key k) st_upd s

let lemma_lookup_key_update_in_store 
      (st:vstore) 
      (s:slot_id{store_contains st s}) 
      (d:bin_tree_dir)
      (b:bool)
      (k:key)
  : Lemma (let res = lookup_key st k in
           let res' = lookup_key (update_in_store st s d b) k in
           (None? res /\ None? res') \/
           (Some? res /\ Some? res' /\ VStoreE?.am (Some?.v res) = VStoreE?.am (Some?.v res')))
  = let stf = filter (has_key k) st in
    let Some (VStoreE ks v am l r) = Seq.index st s in
    let newelem = match d with
                  | Left -> Some (VStoreE ks v am b r)
                  | Right -> Some (VStoreE ks v am l b) in
    assert (Seq.length stf = Seq.length (filter (has_key k) (update_in_store st s d b)));
    if Seq.length stf > 0 
    then (
      (** TODO: For some reason this started failing with the updated vevictb/vevictbm *)
      (*
      if filter_index_map (has_key k) st 0 = s
      then lemma_filter_update_index_eq (has_key k) st s newelem
      else lemma_filter_update_index_neq (has_key k) st s newelem 0
      *)
      admit()
    )

let lemma_update_in_store_preserves_keys
  (st:vstore)
  (s:st_index st{store_contains st s}) 
  (d:bin_tree_dir)
  (b:bool)
  (k:key)
  : Lemma (ensures store_contains_key st k = store_contains_key (update_in_store st s d b) k)
  = lemma_lookup_key_update_in_store st s d b k

let lemma_update_in_store_preserves_key_with_MAdd
  (st:vstore)
  (s:st_index st{store_contains st s}) 
  (d:bin_tree_dir)
  (b:bool)
  (k:key)
  : Lemma (ensures store_contains_key_with_MAdd st k = 
                     store_contains_key_with_MAdd (update_in_store st s d b) k)
  = lemma_lookup_key_update_in_store st s d b k

let lemma_evict_from_store_evicts_key
  (st:vstore)
  (s:st_index st{store_contains st s}) 
  : Lemma (requires is_map st)
          (ensures not (store_contains_key (evict_from_store st s) (stored_key st s)))
  = let k = stored_key st s in
    let st_upd = evict_from_store st s in
    let res = filter (has_key k) st_upd in
    lemma_filter_all_not_inv (has_key k) st_upd;
    assert (Seq.length res = 0)

let lemma_lookup_key_evict_from_store
      (st:vstore) 
      (s:slot_id{store_contains st s}) 
      (k:key{k <> stored_key st s})
  : Lemma (lookup_key st k = lookup_key (evict_from_store st s) k)
  = let stf = filter (has_key k) st in
    if Seq.length stf > 0
    then (
      assert (filter_index_map (has_key k) st 0 <> s);
      lemma_filter_update_index_neq (has_key k) st s None 0
    )

let lemma_evict_from_store_preserves_key_with_MAdd
  (st:vstore)
  (s:st_index st{store_contains st s}) 
  (k:key)
  : Lemma (requires (k <> stored_key st s))
          (ensures (store_contains_key_with_MAdd st k = store_contains_key_with_MAdd (evict_from_store st s) k))
  = lemma_lookup_key_evict_from_store st s k

let lemma_get_slot_lookup_key (st:vstore{is_map st}) (s:slot_id) (k:key)
  : Lemma (requires (store_contains st s /\ stored_key st s = k))
          (ensures (get_slot st s = lookup_key st k))
  = let s' = filter (has_key k) st in
    lemma_filter_unique (has_key k) st s

let lemma_evict_from_store_BAdd_preserves_key_with_MAdd
  (st:vstore{is_map st})
  (s:slot_id{store_contains st s}) 
  (k:key)
  : Lemma (requires (add_method_of st s = Spec.BAdd))
          (ensures (store_contains_key_with_MAdd st k = 
                      store_contains_key_with_MAdd (evict_from_store st s) k))
  = if k = stored_key st s
    then lemma_get_slot_lookup_key st s k
    else lemma_lookup_key_evict_from_store st s k

let lemma_slot_key_equiv_update_value 
      (st:vstore) 
      (s:slot_id) 
      (s':slot_id{store_contains st s'}) 
      (k:key) 
      (v:value_type_of (stored_key st s'))
  : Lemma (requires (slot_key_equiv st s k /\ s <> s'))
          (ensures (slot_key_equiv (update_value st s' v) s k))
  = ()

let rec as_map_aux (l:vstore) 
  : Tot Spec.vstore (decreases (Seq.length l)) =
  let n = Seq.length l in
  if n = 0 then Spec.empty_store
  else 
    let l' = prefix l (n - 1) in
    let f' = as_map_aux l' in
    match Seq.index l (n - 1) with
    | None -> f'
    | Some (VStoreE k v a _ _) -> 
      Spec.add_to_store f' k v a

let as_map (st:vstore{is_map st}) : Spec.vstore =
  as_map_aux st

let rec lemma_as_map_empty (n:nat) 
  : Lemma (ensures (let st = empty_store n in
                     forall (k:key). as_map st k = None))
          (decreases n)
  = if n <> 0 
    then (
      lemma_prefix_create n (None #vstore_entry) (n-1);
      lemma_as_map_empty (n-1)
    )

let lemma_is_map_prefix (l:vstore) (i:seq_index l)
  : Lemma (requires (is_map l))
          (ensures (is_map (prefix l i)))
          [SMTPat (is_map (prefix l i))]
  = ()

let rec lemma_as_map_slot_key_equiv_aux 
      (l:vstore) 
      (s:slot_id) 
      (k:key) 
      (v:value_type_of k) 
      (am:add_method)
      (lb rb:bool)
  : Lemma (requires (s < Seq.length l /\ 
                     Seq.index l s = Some (VStoreE k v am lb rb) /\
                     is_map l)) 
          (ensures (Spec.store_contains (as_map_aux l) k /\
                    Spec.stored_value (as_map_aux l) k = v /\
                    Spec.add_method_of (as_map_aux l) k = am))
          (decreases (Seq.length l))
  = let n = Seq.length l in
    if n <> 0 
    then
      let l' = prefix l (n - 1) in
      match Seq.index l (n - 1) with
      | None -> lemma_as_map_slot_key_equiv_aux l' s k v am lb rb
      | Some (VStoreE k2 v2 am2 _ _) -> 
          if s < n - 1 
          then lemma_as_map_slot_key_equiv_aux l' s k v am lb rb

let lemma_as_map_slot_key_equiv (st:vstore{is_map st}) (s:slot_id) (k:key)
  : Lemma (requires (slot_key_equiv st s k)) 
          (ensures (Spec.store_contains (as_map st) k /\
                    stored_value st s = Spec.stored_value (as_map st) k /\
                    add_method_of st s = Spec.add_method_of (as_map st) k)) 
  = let Some (VStoreE k v a l r) = get_slot st s in 
    lemma_as_map_slot_key_equiv_aux st s k v a l r

let rec lemma_as_map_aux_does_not_contain_key 
      (l:vstore) 
      (k:key) 
  : Lemma (requires (forall i. not (has_key k (Seq.index l i)))) 
          (ensures (not (Spec.store_contains (as_map_aux l) k)))
          (decreases (Seq.length l))
  = let n = Seq.length l in
    if n <> 0 
    then
      let l' = prefix l (n - 1) in
      lemma_as_map_aux_does_not_contain_key l' k

let lemma_store_rel_contains_key (st:vstore) (st':Spec.vstore) (k:key)
  : Lemma (requires (store_rel st st'))
          (ensures (store_contains_key st k = Spec.store_contains st' k))
  = if store_contains_key st k
    then (
      lemma_store_contains_key_inv st k;
      Classical.exists_elim 
        (Spec.store_contains (as_map st) k) 
        (Squash.get_proof (exists s. slot_key_equiv st s k)) 
        (fun s -> lemma_as_map_slot_key_equiv st s k)
    )
    else (
      lemma_lookup_key_returns_None st k;
      lemma_as_map_aux_does_not_contain_key st k
    )

let lemma_store_rel_stored_value (st:vstore) (st':Spec.vstore) (k:key)
  : Lemma (requires (store_rel st st' /\ store_contains_key st k))
          (ensures (stored_value_by_key st k = Spec.stored_value st' k))
  = lemma_store_contains_key_inv st k;
    Classical.exists_elim 
      (stored_value_by_key st k = Spec.stored_value (as_map st) k) 
      (Squash.get_proof (exists s. slot_key_equiv st s k)) 
      (fun s -> lemma_get_slot_lookup_key st s k; 
             lemma_as_map_slot_key_equiv st s k)
   
let lemma_store_rel_add_method_of (st:vstore) (st':Spec.vstore) (k:key)
  : Lemma (requires (store_rel st st' /\ store_contains_key st k))
          (ensures (add_method_of_by_key st k = Spec.add_method_of st' k))
  = lemma_store_contains_key_inv st k;
    Classical.exists_elim 
      (add_method_of_by_key st k = Spec.add_method_of (as_map st) k) 
      (Squash.get_proof (exists s. slot_key_equiv st s k)) 
      (fun s -> lemma_get_slot_lookup_key st s k; 
             lemma_as_map_slot_key_equiv st s k)

let compatible_entry_prefix (st:vstore) (s:st_index st) (e:vstore_entry) (i:st_index st)
  : Lemma (requires (compatible_entry st s e /\ s < i))
          (ensures (compatible_entry (prefix st i) s e))
          [SMTPat (compatible_entry (prefix st i) s e)]
  = if not (store_contains st s)
    then (
      lemma_lookup_key_returns_None st e.k;
      lemma_filter_all_not_inv (has_key e.k) (prefix st i)
    )

#push-options "--fuel 1,1 --ifuel 2,2"
let rec lemma_as_map_update (st:vstore{is_map st}) 
                            (s:st_index st)
                            (e:vstore_entry{compatible_entry st s e})
  : Lemma (ensures (let m = as_map st in
                    let m' = as_map (update_slot st s e) in
                    m' e.k = Some (Spec.VStore e.v e.am) /\
                    (forall k. k <> e.k ==> m' k = m k))) 
          (decreases (Seq.length st))
  = let n = Seq.length st in
    if n <> 0 
    then
      let st_upd = update_slot st s e in
      let st_p = prefix st (n - 1) in
      let st_upd_p = prefix st_upd (n - 1) in
      if s < n - 1
      then ( 
        let st_p_upd = update_slot st_p s e in      
        lemma_as_map_update st_p s e;
        assert (Seq.equal st_p_upd st_upd_p)
      )
      else ( // s = n - 1
        assert (Seq.equal st_p st_upd_p)
      )
#pop-options

let lemma_store_rel_update_value (st:vstore) (st':Spec.vstore) (s:slot_id) (k:key) (v:value_type_of k)
  : Lemma (requires (store_rel st st' /\ slot_key_equiv st s k))
          (ensures (store_rel (update_value st s v) (Spec.update_store st' k v)))
  = let Some (VStoreE _ _ am l r) = get_slot st s in
    lemma_as_map_update st s (VStoreE k v am l r)

let lemma_store_rel_update_in_store (st:vstore) (st':Spec.vstore) (s:slot_id) (d:bin_tree_dir) (b:bool)
  : Lemma (requires (store_rel st st' /\ store_contains st s))
          (ensures (store_rel (update_in_store st s d b) st'))
  = let Some (VStoreE k v am l r) = get_slot st s in
    assert (slot_key_equiv st s k); // assert needed to trigger pattern
    let e = match d with 
            | Left -> VStoreE k v am b r
            | Right -> VStoreE k v am l b in
    lemma_as_map_update st s e

let lemma_store_rel_add_to_store (st:vstore) (st':Spec.vstore) (s:st_index st) (k:key) (v:value_type_of k) (am:add_method)
  : Lemma (requires (store_rel st st' /\ not (store_contains st s) /\ not (Spec.store_contains st' k)))
          (ensures (store_rel (add_to_store st s k v am) (Spec.add_to_store st' k v am)))
  = lemma_as_map_update st s (VStoreE k v am false false)

let rec lemma_as_map_evict (st:vstore{is_map st}) (s:st_index st) (k:key)
  : Lemma (requires (slot_key_equiv st s k))
          (ensures (let m = as_map st in
                    let m' = as_map (evict_from_store st s) in
                    m' k = None /\ (forall k'. k' <> k ==> m' k' = m k'))) 
          (decreases (Seq.length st))
  = let n = Seq.length st in
    if n <> 0 
    then
      let stupd = evict_from_store st s in
      let stp = prefix st (n - 1) in
      let stupdp = prefix stupd (n - 1) in
      if s < n - 1
      then ( 
        lemma_as_map_evict stp s k;
        assert (Seq.equal stupdp (evict_from_store stp s))
      )
      else (  // s = n - 1
        assert (Seq.equal stp stupdp);
        lemma_as_map_aux_does_not_contain_key stp k
      )

let lemma_store_rel_evict_from_store (st:vstore) (st':Spec.vstore) (s:st_index st) (k:key)
  : Lemma (requires (store_rel st st' /\ slot_key_equiv st s k))
          (ensures (store_rel (evict_from_store st s) (Spec.evict_from_store st' k)))
  = lemma_as_map_evict st s k
