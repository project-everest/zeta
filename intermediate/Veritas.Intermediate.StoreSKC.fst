module Veritas.Intermediate.StoreSKC

let get_slot (st:vstore) (s:slot_id)
  : option vstore_entry
  = if s >= Seq.length st.data then None 
    else Seq.index st.data s

let store_contains (st:vstore) (s:slot_id) : bool
  = Some? (get_slot st s)

let store_contains_st_index (st:vstore) (s:slot_id{store_contains st s})
  : Lemma (s < Seq.length st.data)
  = ()

let stored_key (st:vstore) (s:slot_id{store_contains st s}) : key
  = VStoreE?.k (Some?.v (get_slot st s))

let stored_value (st:vstore) (s:slot_id{store_contains st s}) : value
  = VStoreE?.v (Some?.v (get_slot st s))

let stored_value_matches_stored_key (st:vstore) (s:slot_id{store_contains st s}) 
  : Lemma (is_value_of (stored_key st s) (stored_value st s))
          [SMTPat (stored_value st s)]
  = ()

let add_method_of (st:vstore) (s:slot_id{store_contains st s}) : add_method
  = VStoreE?.am (Some?.v (get_slot st s))

let lookup_key (st:vstore) (k:key) 
  : option vstore_entry
  = let f ro = if None? ro then false
               else let Some r = ro in r.k = k in
    let s' = filter f st.data in
    if Seq.length s' = 0 then None
    else Seq.index s' 0 

let store_contains_key (st:vstore) (k:key) : bool
  = Some? (lookup_key st k)

let lemma_lookup_key_returns_k (st:vstore) (k:key) 
  : Lemma (requires (store_contains_key st k))
          (ensures (VStoreE?.k (Some?.v (lookup_key st k)) = k))
  = let f ro = if None? ro then false
               else let Some r = ro in r.k = k in
    lemma_filter_correct1 f st.data 0

let lemma_lookup_key_returns_None (st:vstore) (k:key)
  : Lemma (requires (lookup_key st k = None))
          (ensures (let f ro = if None? ro then false
                               else let Some r = ro in r.k = k in
                    forall i. not (f (Seq.index st.data i))))
  = let f ro = if None? ro then false
               else let Some r = ro in r.k = k in
    let s' = filter f st.data in
    if Seq.length s' = 0 
    then lemma_filter_all_not f st.data
    else lemma_filter_correct1 f st.data 0

let lemma_store_contains_key (st:vstore) (k:key)
  : Lemma (requires (exists s. stored_key st s = k))
          (ensures (store_contains_key st k))
  = let f ro = if None? ro then false
               else let Some r = ro in r.k = k in
    lemma_filter_exists f st.data;
    lemma_filter_correct1 f st.data 0

(* Opposite direction of previous lemma *)
let lemma_store_contains_key_inv (st:vstore) (k:key)
  : Lemma (requires (store_contains_key st k))
          (ensures (exists s. stored_key st s = k))
  = let f ro = if None? ro then false
               else let Some r = ro in r.k = k in
    let s' = filter f st.data in
    if Seq.length s' > 0 
    then 
      let i = filter_index_map f st.data 0 in
      assert (stored_key st i = k)

let lemma_get_slot_lookup_key (st:vstore{st.is_map}) (s:slot_id) (k:key)
  : Lemma (requires (store_contains st s /\ stored_key st s = k))
          (ensures (get_slot st s = lookup_key st k))
  = // relies on the fact that (filter f st.data) returns a unique elmt
    admit()

let stored_value_by_key (st:vstore) (k:key{store_contains_key st k})
  : value_type_of k
  = lemma_lookup_key_returns_k st k;
    VStoreE?.v (Some?.v (lookup_key st k))

let add_method_of_by_key (st:vstore) (k:key{store_contains_key st k})
  : add_method
  = VStoreE?.am (Some?.v (lookup_key st k))

(* Two cases where it's safe to add an entry (e) to the store (st) at s: 
   * e.k is not in st
   * e.k is already at s *)
let compatible_entry (st:vstore) (s:st_index st) (e:vstore_entry) : Type
  = not (store_contains_key st e.k) \/ 
    (store_contains st s /\ stored_key st s = e.k) 

let lemma_not_contains_key (st:vstore) (k:key) (s:slot_id{store_contains st s})
  : Lemma (requires (not (store_contains_key st k)))
          (ensures (stored_key st s <> k))
  = ()

let lemma_add_entry_case_1 (st:vstore) (s:st_index st) (e:vstore_entry)
  : Lemma (requires (st.is_map /\ not (store_contains_key st e.k)))
          (ensures (is_map_f (Seq.upd st.data s (Some e))))
  = let l = Seq.upd st.data s (Some e) in
    let aux (i:seq_index l{Some? (Seq.index l i)})
            (i':seq_index l{Some? (Seq.index l i') /\ i <> i'})
          : Lemma (VStoreE?.k (Some?.v (Seq.index l i)) <> VStoreE?.k (Some?.v (Seq.index l i')))
                  [SMTPat (Seq.index l i); SMTPat (Seq.index l i')]
          = if i = s 
            then lemma_not_contains_key st e.k i' 
            else if i' = s 
                 then lemma_not_contains_key st e.k i in
    assert (is_map_f l)

let lemma_add_entry_case_2 (st:vstore) (s:st_index st) (e:vstore_entry)
  : Lemma (requires (st.is_map /\ store_contains st s /\ stored_key st s = e.k))
          (ensures (is_map_f (Seq.upd st.data s (Some e))))
  = () 

let update_slot (st:vstore) (s:st_index st) (e:vstore_entry{compatible_entry st s e})
  : vstore
  = if st.is_map 
    then if not (store_contains_key st e.k) 
         then lemma_add_entry_case_1 st s e 
         else if store_contains st s && stored_key st s = e.k
              then lemma_add_entry_case_2 st s e;
    VStore (Seq.upd st.data s (Some e)) st.is_map

let update_store 
  (st:vstore)
  (s:slot_id{store_contains st s}) 
  (v:value_type_of (stored_key st s))
  : Tot (st':vstore {store_contains st' s /\
                     stored_value st' s = v})
  = let Some (VStoreE k _ am) = get_slot st s in
    update_slot st s (VStoreE k v am) 
  
let update_store_preserves_length 
      (st:vstore) 
      (s:slot_id{store_contains st s}) 
      (v:value_type_of (stored_key st s)) 
  : Lemma (let st' = update_store st s v in
           Seq.length st.data = Seq.length st'.data)
  = ()

let lemma_update_store_preserves_is_map (st:vstore) s v
  : Lemma (let st' = update_store st s v in 
           st.is_map = st'.is_map)
  = ()

let add_to_store 
      (st:vstore) 
      (s:st_index st) 
      (k:key) 
      (v:value_type_of k) 
      (am:add_method)
  : Tot (st':vstore {store_contains st' s /\
                     stored_key st' s = k /\
                     stored_value st' s = v /\
                     add_method_of st' s = am})
  = let e = VStoreE k v am in
    if not (store_contains_key st k)
    then update_slot st s e
    else VStore (Seq.upd st.data s (Some e)) false

let lemma_add_to_store_is_map1 (st:vstore) s k v am
  : Lemma (requires (not (store_contains_key st k)))
          (ensures (let st' = add_to_store st s k v am in 
                    st.is_map = st'.is_map))
  = ()

let lemma_add_to_store_is_map2 (st:vstore) s k v am
  : Lemma (requires (store_contains_key st k))
          (ensures (let st' = add_to_store st s k v am in 
                    st'.is_map = false))
  = ()

let evict_from_store (st:vstore) (s:st_index st)
  : Tot (st':vstore {not (store_contains st' s)})
  = VStore (Seq.upd st.data s None) st.is_map

let lemma_evict_from_store_preserves_is_map (st:vstore) (s:st_index st)
  : Lemma (let st' = evict_from_store st s in
           st.is_map = st'.is_map)
  = ()

let lemma_slot_key_equiv_update_store 
      (st:vstore) 
      (s:slot_id) 
      (s':slot_id{store_contains st s'}) 
      (k:key) 
      (v:value_type_of (stored_key st s'))
  : Lemma (requires (slot_key_equiv st s k /\ s <> s'))
          (ensures (slot_key_equiv (update_store st s' v) s k))
  = ()

let rec as_map_aux (l:vstore_data) 
  : Tot Spec.vstore (decreases (Seq.length l)) =
  let n = Seq.length l in
  if n = 0 then fun _ -> None
  else 
    let l' = prefix l (n - 1) in
    let f' = as_map_aux l' in
    match Seq.index l (n - 1) with
    | None -> f'
    | Some (VStoreE k v a) -> 
      fun (k':key) -> if k = k' then Some (Spec.VStore v a) else f' k' 

let as_map (st:vstore{st.is_map}) : Spec.vstore =
  as_map_aux st.data

let rec lemma_as_map_empty (n:nat) 
  : Lemma (ensures (let st = VStore (Seq.create n None) true in
                     forall (k:key). as_map st k = None))
          (decreases n)
  = if n <> 0 
    then (
      lemma_prefix_create n (None #vstore_entry) (n-1);
      lemma_as_map_empty (n-1)
    )

let lemma_is_map_f_prefix (l:vstore_data) (i:seq_index l)
  : Lemma (requires (is_map_f l))
          (ensures (is_map_f (prefix l i)))
          [SMTPat (is_map_f (prefix l i))]
  = ()

let rec lemma_as_map_slot_key_equiv_aux 
      (l:vstore_data) 
      (s:slot_id) 
      (k:key) 
      (v:value_type_of k) 
      (am:add_method)
  : Lemma (requires (s < Seq.length l /\ 
                     Seq.index l s = Some (VStoreE k v am) /\
                     is_map_f l)) 
          (ensures (Spec.store_contains (as_map_aux l) k /\
                    Spec.stored_value (as_map_aux l) k = v /\
                    Spec.add_method_of (as_map_aux l) k = am))
          (decreases (Seq.length l))
  = let n = Seq.length l in
    if n <> 0 
    then
      let l' = prefix l (n - 1) in
      match Seq.index l (n - 1) with
      | None -> lemma_as_map_slot_key_equiv_aux l' s k v am
      | Some (VStoreE k2 v2 am2) -> 
          if s < n - 1 
          then lemma_as_map_slot_key_equiv_aux l' s k v am

let lemma_as_map_slot_key_equiv (st:vstore{st.is_map}) (s:slot_id) (k:key)
  : Lemma (requires (slot_key_equiv st s k)) 
          (ensures (Spec.store_contains (as_map st) k /\
                    stored_value st s = Spec.stored_value (as_map st) k /\
                    add_method_of st s = Spec.add_method_of (as_map st) k)) 
  = let Some (VStoreE k v a) = get_slot st s in 
    lemma_as_map_slot_key_equiv_aux st.data s k v a

let rec lemma_as_map_aux_does_not_contain_key 
      (l:vstore_data) 
      (k:key) 
  : Lemma (requires (let f ro = if None? ro then false
                                else let Some r = ro in r.k = k in
                     forall i. not (f (Seq.index l i)))) 
          (ensures (not (Spec.store_contains (as_map_aux l) k)))
          (decreases (Seq.length l))
  = let n = Seq.length l in
    if n <> 0 
    then
      let l' = prefix l (n - 1) in
      lemma_as_map_aux_does_not_contain_key l' k

let lemma_as_map_contains_key (st:vstore{st.is_map}) (k:key)
  : Lemma (store_contains_key st k = Spec.store_contains (as_map st) k)
  = if store_contains_key st k
    then (
      lemma_store_contains_key_inv st k;
      Classical.exists_elim 
        (Spec.store_contains (as_map st) k) 
        (Squash.get_proof (exists s. slot_key_equiv st s k)) 
        (fun s -> lemma_as_map_slot_key_equiv st s k)
    )
    else (
      let f ro = if None? ro then false
                 else let Some r = ro in r.k = k in
      lemma_lookup_key_returns_None st k;
      lemma_as_map_aux_does_not_contain_key st.data k
    )

let lemma_as_map_stored_value (st:vstore{st.is_map}) (k:key)
  : Lemma (requires (store_contains_key st k))
          (ensures (stored_value_by_key st k = Spec.stored_value (as_map st) k))
  = lemma_store_contains_key_inv st k;
    Classical.exists_elim 
      (stored_value_by_key st k = Spec.stored_value (as_map st) k) 
      (Squash.get_proof (exists s. slot_key_equiv st s k)) 
      (fun s -> lemma_get_slot_lookup_key st s k; 
             lemma_as_map_slot_key_equiv st s k)
   
let lemma_as_map_add_method_of (st:vstore{st.is_map}) (k:key)
  : Lemma (requires (store_contains_key st k))
          (ensures (add_method_of_by_key st k = Spec.add_method_of (as_map st) k))
  = lemma_store_contains_key_inv st k;
    Classical.exists_elim 
      (add_method_of_by_key st k = Spec.add_method_of (as_map st) k) 
      (Squash.get_proof (exists s. slot_key_equiv st s k)) 
      (fun s -> lemma_get_slot_lookup_key st s k; 
             lemma_as_map_slot_key_equiv st s k)
