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
  = VStore?.k (Some?.v (get_slot st s))

let stored_value (st:vstore) (s:slot_id{store_contains st s}) : value
  = VStore?.v (Some?.v (get_slot st s))

let stored_value_matches_stored_key (st:vstore) (s:slot_id{store_contains st s}) 
  : Lemma (is_value_of (stored_key st s) (stored_value st s))
  = ()

let add_method_of (st:vstore) (s:slot_id{store_contains st s}) : add_method
  = VStore?.am (Some?.v (get_slot st s))

let lookup_key (st:vstore) (k:key) 
  : option vstore_entry
  = let f ro = if None? ro then false
               else let Some r = ro in VStore?.k r = k in
    let s = filter f st.data in
    if Seq.length s = 0 then None
    else Seq.index s 0 

let store_contains_key (st:vstore) (k:key) : bool
  = Some? (lookup_key st k)

let lemma_lookup_key (st:vstore) (k:key) 
  : Lemma (requires (store_contains_key st k))
          (ensures (VStore?.k (Some?.v (lookup_key st k)) = k))
  = let f ro = if None? ro then false
               else let Some r = ro in VStore?.k r = k in
    lemma_filter_correct1 f st.data 0

let lemma_store_contains_key (st:vstore) (k:key)
  : Lemma (requires (exists s. stored_key st s = k))
          (ensures (store_contains_key st k))
  = let f ro = if None? ro then false
               else let Some r = ro in VStore?.k r = k in
    lemma_filter_exists f st.data;
    lemma_filter_correct1 f st.data 0

let stored_value_by_key (st:vstore) (k:key{store_contains_key st k})
  : value_type_of k
  = lemma_lookup_key st k;
    VStore?.v (Some?.v (lookup_key st k))

let add_method_of_by_key (st:vstore) (k:key{store_contains_key st k})
  : add_method
  = VStore?.am (Some?.v (lookup_key st k))

let update_slot (st:vstore) (s:st_index st) (e:vstore_entry)
  : vstore
  = { st with data = Seq.upd st.data s (Some e) }

let update_store 
  (st:vstore) 
  (s:slot_id{store_contains st s}) 
  (v:value_type_of (stored_key st s))
  : Tot (st':vstore {store_contains st' s /\
                     stored_value st' s = v})
  = let Some (VStore k _ am) = get_slot st s in
    update_slot st s (VStore k v am) 

let update_store_preserves_length 
      (st:vstore) 
      (s:slot_id{store_contains st s}) 
      (v:value_type_of (stored_key st s)) 
  : Lemma (let st' = update_store st s v in
           Seq.length st.data = Seq.length st'.data)
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
  = update_slot st s (VStore k v am)

let evict_from_store (st:vstore) (s:st_index st)
  : Tot (st':vstore {not (store_contains st' s)})
  = { st with data = Seq.upd st.data s None }

let rec as_map_aux (l:Seq.seq (option vstore_entry)) 
  : Tot Spec.vstore (decreases (Seq.length l)) =
  let n = Seq.length l in
  if n = 0 then fun _ -> None
  else 
    let l' = prefix l (n - 1) in
    let f' = as_map_aux l' in
    match Seq.index l (n - 1) with
    | None -> f'
    | Some (VStore k v a) -> 
      fun (k':key) -> if k = k' then Some (Spec.VStore v a) else f' k' 

let as_map (st:vstore{st.is_map}) : Spec.vstore =
  as_map_aux st.data

let rec lemma_as_map_slot_key_equiv_aux 
      (l:Seq.seq (option vstore_entry)) 
      (s:seq_index l) 
      (k:key) 
      (v:value_type_of k) 
      (am:add_method)
  : Lemma (requires (Seq.index l s = Some (VStore k v am))) 
          (ensures (Spec.store_contains (as_map_aux l) k /\
                    Spec.stored_value (as_map_aux l) k = v))
          (decreases (Seq.length l))
  = let n = Seq.length l in
    if n <> 0 
    then
      let l' = prefix l (n - 1) in
      let f' = as_map_aux l' in
      match Seq.index l (n - 1) with
      | None -> lemma_as_map_slot_key_equiv_aux l' s k v am
      | Some (VStore _ _ _) -> 
          if s < n - 1 
          then (
                 lemma_as_map_slot_key_equiv_aux l' s k v am;
                 // I thought the recursive call would work...
                 admit()
               )

let lemma_as_map_slot_key_equiv (st:vstore{st.is_map}) (s:slot_id) (k:key)
  : Lemma (requires (slot_key_equiv st s k)) 
          (ensures (Spec.store_contains (as_map st) k /\
                    stored_value st s = Spec.stored_value (as_map st) k)) 
  = let Some (VStore k v a) = get_slot st s in 
    lemma_as_map_slot_key_equiv_aux st.data s k v a
