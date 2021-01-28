module Veritas.Intermediate.Store
open FStar.Classical

let update_slot #vcfg (st:vstore_raw vcfg) (s:slot_id vcfg) (e:vstore_entry vcfg)
  : vstore_raw _
  = Seq.upd st s (Some e)

let update_value_raw #vcfg (st:vstore vcfg) (s:inuse_slot_id st) (v:value_type_of (stored_key st s))
  : vstore_raw vcfg = 
  let VStoreE k v' am lp rp = get_inuse_slot st s in
  let e' = VStoreE k v am lp rp in
  update_slot st s e'

let lemma_update_value_identical_except 
  #vcfg (st:vstore vcfg) (s:inuse_slot_id st) (v:value_type_of (stored_key st s))
  : Lemma (ensures (let st' = update_value_raw st s v in 
                    identical_except st st' s)) = 
  let st' = update_value_raw st s v in                    
  let aux (s': slot_id vcfg)
    : Lemma (ensures (s' <> s ==> get_slot st s' = get_slot st' s'))
            [SMTPat (get_slot st s' = get_slot st' s')]
    = 
    ()
  in
  ()

let points_to_unchanged_slot #vcfg (st1 st2: vstore_raw vcfg) (s: slot_id vcfg) = 
  inuse_slot st1 s = inuse_slot st2 s /\
  (inuse_slot st1 s ==> points_to_info st1 s Left = points_to_info st2 s Left /\
                       points_to_info st1 s Right = points_to_info st2 s Right)
                       
let points_to_unchanged #vcfg (st1 st2: vstore_raw vcfg) = 
  forall (s: slot_id vcfg). {:pattern points_to_unchanged_slot st1 st2 s} 
                       points_to_unchanged_slot st1 st2 s

let lemma_points_to_unchanged_implies_points_to_inuse #vcfg (st1 st2: vstore_raw vcfg) (s1 s2: slot_id _)
  : Lemma (requires (points_to_unchanged st1 st2))
          (ensures (points_to_inuse_local st1 s1 s2 <==> points_to_inuse_local st2 s1 s2)) = 
  assert(points_to_unchanged_slot st1 st2 s1);          
  assert(points_to_unchanged_slot st1 st2 s2); // inuse_slot st1 s2 = inuse_slot st2 s2
  ()

let slot_dir vcfg = (slot_id vcfg) & bin_tree_dir

/// Computational version of pointed_to_inv_local
///
let rec pointed_to_inv_local_find_aux #vcfg (st: vstore_raw vcfg) 
                                        (s: slot_id vcfg{pointed_to_inv_local st s /\
                                                         inuse_slot st s /\
                                                         stored_key st s <> Root /\
                                                         add_method_of st s = Spec.MAdd})
                                        (sl: nat{sl <= store_size vcfg})     // slot limit 
  : (r:option (slot_dir vcfg){r = None /\
                              (forall (s1:slot_id vcfg{s < sl}). forall (d:bin_tree_dir). 
                                empty_slot st s1 \/
                                points_to_none st s1 d \/ 
                                pointed_slot st s1 d <> s) \/
                              Some? r /\ (let (s1,d) = Some?.v r in
                                          inuse_slot st s1 /\
                                          points_to_some_slot st s1 d /\
                                          pointed_slot st s1 d = s)})
  = admit()

let pointed_to_inv_local_find #vcfg (st: vstore_raw vcfg) 
                                    (s: slot_id vcfg{pointed_to_inv_local st s /\
                                                         inuse_slot st s /\
                                                         stored_key st s <> Root /\
                                                         add_method_of st s = Spec.MAdd})
                                        (sl: nat{sl <= store_size vcfg})     // slot limit 
  : (sd: (slot_dir vcfg){let (s1,d) = sd in
                         inuse_slot st s1 /\
                         points_to_some_slot st s1 d /\
                         pointed_slot st s1 d = s})
  = 
  let r = pointed_to_inv_local_find_aux st s (store_size vcfg) in
  if r = None then (
    assert(pointed_to_inv_local st s);
    let aux (d:bin_tree_dir)
      : Lemma (ensures (forall (s':inuse_slot_id st). ~ (points_to_some_slot st s' d /\ pointed_slot st s' d = s)))
      = 
      let aux2 (s':inuse_slot_id st):
        Lemma (ensures (~ (points_to_some_slot st s' d /\ pointed_slot st s' d = s)))
        = 
        assert(empty_slot st s' \/
               points_to_none st s' d \/ 
               pointed_slot st s' d <> s);
        ()
      in
      forall_intro aux2      
    in
    forall_intro aux;
    // assert (forall (s':inuse_slot_id st) (d:bin_tree_dir). ~ (points_to_some_slot st s' d /\ pointed_slot st s' d = s));
    // assert(False);
    (0,Left)
  )
  else Some?.v r

let update_value 
  (#vcfg:_)
  (st:vstore vcfg)
  (s:inuse_slot_id st)
  (v:value_type_of (stored_key st s))
  : Tot (st':vstore vcfg {identical_except st st' s /\
                          inuse_slot st' s /\
                          v = stored_value st' s /\
                          (let VStoreE k1 _ am1 ld1 rd1 = get_inuse_slot st s in
                           let VStoreE k2 _ am2 ld2 rd2 = get_inuse_slot st' s in
                           k1 = k2 /\ am1 = am2 /\ ld1 = ld2 /\ rd1 = rd2)}) = 
  let st' = update_value_raw st s v in
  lemma_update_value_identical_except st s v;
  assert(inuse_slot st' s);
  let v = stored_value st' s in
  let VStoreE k1 _ am1 ld1 rd1 = get_inuse_slot st s in
  let VStoreE k2 _ am2 ld2 rd2 = get_inuse_slot st' s in
  assert(k1 = k2);
  assert(am1 = am2);
  assert(ld1 = ld2);
  assert(rd1 = rd2);
  admit()

let madd_to_store
  (#vcfg: verifier_config)
  (st:vstore vcfg)
  (s:empty_slot_id st)
  (k:key) (v:value_type_of k)
  (s':merkle_slot_id st)
  (d:bin_tree_dir {points_to_none st s' d})
  : Tot (st':vstore vcfg{let od = other_dir d in
                         identical_except2 st st' s s' /\     // st and st' are identical except at s, s'

                         // nothing changes in slot s' except it now points to s in direction d
                         inuse_slot st' s' /\
                         stored_key st' s' = stored_key st s' /\
                         stored_value st' s' = stored_value st s' /\
                         add_method_of st' s' = add_method_of st s' /\
                         points_to_dir st' s' d s /\
                         points_to_info st' s' od = points_to_info st s' od /\

                         // slot s contains (k, v, MAdd) and points to nothing
                         inuse_slot st' s /\
                         get_inuse_slot st' s = VStoreE k v Spec.MAdd None None                         
                         })

  = admit()

let madd_to_store_split 
  (#vcfg: verifier_config)
  (st:vstore vcfg)
  (s:empty_slot_id st)
  (k:key) (v:value_type_of k)
  (s':merkle_slot_id st)
  (d:bin_tree_dir {points_to_some_slot st s' d})
  (d2:bin_tree_dir)
  : Tot (st': vstore vcfg{let od = other_dir d in        
                          let s2 = pointed_slot st s' d in
                          let od2 = other_dir d2 in
                          
                          // st and st' identical except at s, s'
                          identical_except2 st st' s s' /\

                          // nothing changes in slot s', except it now points to s in direction d 
                          inuse_slot st' s' /\
                          stored_key st' s' = stored_key st s' /\
                          stored_value st' s' = stored_value st s' /\
                          add_method_of st' s' = add_method_of st s' /\
                          points_to_dir st' s' d s /\
                          points_to_info st' s' od = points_to_info st s' od /\

                          // slot s contains (k, v, MAdd) and points to s2 along direction d2
                          inuse_slot st' s /\
                          stored_key st' s = k /\ stored_value st' s = v /\ add_method_of st' s = Spec.MAdd /\
                          points_to_none st' s od2 /\
                          points_to_dir st' s d2 s2})
  = admit()

let madd_to_store_root
  (#vcfg: verifier_config)
  (st:vstore vcfg)
  (s:empty_slot_id st)
  (v:value_type_of Root)
  : Tot (st':vstore vcfg{// st and st' identical except at s, s'
                         identical_except st st' s /\

                         // slot s contains (Root, v, MAdd) and points to none 
                         inuse_slot st' s /\
                         get_inuse_slot st' s = VStoreE Root v Spec.MAdd None None})                        
  = admit()

let badd_to_store 
      (#vcfg:verifier_config)
      (st:vstore vcfg) 
      (s:empty_slot_id st)
      (k:key) 
      (v:value_type_of k) 
  : Tot (st':vstore vcfg {// st and st' identical except for s
                          identical_except st st' s /\
                          inuse_slot st' s /\
                          get_inuse_slot st' s = VStoreE k v Spec.BAdd None None})
  = admit()

let mevict_from_store 
  (#vcfg: verifier_config)
  (st:vstore vcfg)
  (s:inuse_slot_id st{points_to_none st s Left /\ points_to_none st s Right})  
  (s':inuse_slot_id st)
  (d:bin_tree_dir{points_to_dir st s' d s})
  : Tot (st':vstore vcfg {let od = other_dir d in
                          
                          // st and st' identical except at s, s'
                          identical_except2 st st' s s' /\

                          // slot s is empty after update
                          empty_slot st' s /\

                          // nothing changes in slot s', except it points to none in directoin d
                          inuse_slot st' s' /\
                          stored_key st' s' = stored_key st s /\
                          stored_value st' s' = stored_value st s' /\
                          add_method_of st' s' = add_method_of st s' /\
                          points_to_info st' s' od = points_to_info st s' od /\
                          points_to_none st' s' d
                          })
  = admit()

let bevict_from_store
  (#vcfg: verifier_config)
  (st:vstore vcfg)
  (s:inuse_slot_id st{points_to_none st s Left /\ points_to_none st s Right})
  : Tot (st':vstore vcfg {// st and st' are identical except at slot s 
                          identical_except st st' s /\

                          // slot s is empty after the update
                          empty_slot st' s})
  = admit()


let store_contains_key (#vcfg:_) (st:vstore vcfg) (k:key): bool  = admit()

let lemma_stored_key_implies_contains (#vcfg:_) (st: vstore vcfg) (s:inuse_slot_id st):
  Lemma (ensures (store_contains_key st (stored_key st s)))
  = admit()


let slot_of_key (#vcfg:_) (st:vstore vcfg) (k:key{store_contains_key st k}): 
  (s:inuse_slot_id st{stored_key st s = k}) = admit()

let stored_value_by_key  (#vcfg:_) (st:vstore vcfg) (k:key{store_contains_key st k}) : value_type_of k
  = admit()

let add_method_of_by_key (#vcfg:_) (st:vstore vcfg) (k:key{store_contains_key st k}) : add_method
  = admit()

let pointing_slot (#vcfg:_) 
                (st:vstore vcfg) 
                (s:inuse_slot_id st{Root <> stored_key st s /\ add_method_of st s = Spec.MAdd})
 : Tot (s':inuse_slot_id st{points_to st s' s}) = admit()


let lemma_ismap_update_value
      (#vcfg:_)
      (st:ismap_vstore vcfg)
      (s:inuse_slot_id st)
      (v:value_type_of (stored_key st s))
  : Lemma (ensures (is_map (update_value st s v)))
  = admit()

let lemma_ismap_correct (#vcfg:_) (st:ismap_vstore vcfg) (s1 s2: inuse_slot_id st)
  : Lemma (requires (stored_key st s1 = stored_key st s2))
          (ensures (s1 = s2))
  = admit()
  
let as_map (#vcfg:_) (st:ismap_vstore vcfg) : Spec.vstore = admit()

let lemma_as_map_empty (vcfg:_)
  : Lemma (ensures (let st = empty_store vcfg in
                     forall (k:key). as_map st k = None)) = admit()

let lemma_as_map_slot_key_equiv (#vcfg:_) (st:ismap_vstore vcfg) (s:slot_id vcfg) (k:key)
  : Lemma (requires (slot_key_equiv st s k)) 
          (ensures (Spec.store_contains (as_map st) k /\
                    stored_value st s = Spec.stored_value (as_map st) k /\
                    add_method_of st s = Spec.add_method_of (as_map st) k))
  = admit()

let lemma_as_map_slot_key_equiv2 (#vcfg:_) (st:ismap_vstore vcfg) (s:inuse_slot_id _)
  : Lemma (ensures (let k = stored_key st s in
                    let stk = as_map st in
                    Spec.store_contains stk k /\
                    stored_value st s = Spec.stored_value stk k /\
                    add_method_of st s = Spec.add_method_of stk k)) = admit()


let lemma_store_rel_contains_key (#vcfg:_) (st:vstore vcfg) (st':Spec.vstore) (k:key)
  : Lemma (requires (store_rel st st'))
          (ensures (store_contains_key st k = Spec.store_contains st' k))
  = admit()

let lemma_store_rel_stored_value (#vcfg:_) (st:vstore vcfg) (st':Spec.vstore) (k:key)
  : Lemma (requires (store_rel st st' /\ store_contains_key st k))
          (ensures (stored_value_by_key st k = Spec.stored_value st' k))
  = admit()

let lemma_store_rel_add_method_of (#vcfg:_) (st:vstore vcfg) (st':Spec.vstore) (k:key)
  : Lemma (requires (store_rel st st' /\ store_contains_key st k))
          (ensures (add_method_of_by_key st k = Spec.add_method_of st' k))
  = admit()

let lemma_store_rel_update_value (#vcfg:_) (st:vstore vcfg) (st':Spec.vstore) (s:slot_id vcfg) (k:key) (v:value_type_of k)
  : Lemma (requires (store_rel st st' /\ slot_key_equiv st s k))
          (ensures (store_rel (update_value st s v) (Spec.update_store st' k v)))
  = admit()



(*
(* update the data value of a data key *)
let update_data_value 
  (st:vstore)
  (s:data_slot_id st)
  (v:value{DVal? v})
  : Tot (st':vstore {Seq.length st = Seq.length st' /\
                     inuse_slot st' s /\
                     stored_value st' s = v}) = 
  assert(not (desc_in_store st s Left));
  assert(not (desc_in_store st s Right));
  let Some (VStoreE k _ am _ _) = get_slot st s in
  let st' = update_slot st s (VStoreE k v am None None) in
  assert(Seq.length st = Seq.length st');
  assert(inuse_slot st' s);
  assert(stored_value st' s = v);

  let aux1 (s0:slot_id st'):
    Lemma (ensures (inuse_slot st' s0 = inuse_slot st s0 /\
                    (inuse_slot st' s0 ==> 
                     stored_key st' s0 = stored_key st s0))) = ()
  in

  let aux (s0:slot_id st'):
    Lemma (ensures (store_inv_slot st' s0))
          [SMTPat (store_inv_slot st' s0)] = 
    if s0 = s then ()
    else (
      assert(Seq.index st s0 = Seq.index st' s0);
      if empty_slot st s0 then ()
      else if is_data_key (stored_key st s0) then ()
      else
        admit()
    )
    in
  assert(store_inv_local st');
  st'


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
*)
