module Veritas.Intermediate.StoreS

open Veritas.BinTree
open Veritas.Key
open Veritas.Record
open Veritas.SeqAux

module Spec = Veritas.Verifier
module FE = FStar.FunctionalExtensionality

let slot_id = nat
let add_method = Veritas.Verifier.add_method

(* l_in_store/r_in_store record whether this entry was used as a merkle parent to add 
   a left or right child *)
type vstore_entry = 
  | VStoreE: k:key -> 
             v:value_type_of k -> 
             am:add_method -> 
             l_in_store : bool -> 
             r_in_store : bool -> 
             vstore_entry

type vstore_data = Seq.seq (option vstore_entry) 

(* No duplicate keys in the store *)
let is_map_f (s:vstore_data) =
  forall (i:seq_index s{Some? (Seq.index s i)}) 
    (i':seq_index s{Some? (Seq.index s i') /\ i <> i'}). 
        {:pattern (Seq.index s i); (Seq.index s i')}
    (VStoreE?.k (Some?.v (Seq.index s i)) <> VStoreE?.k (Some?.v (Seq.index s i')))

let elim_is_map_f (s:vstore_data) 
                  (i:seq_index s{Some? (Seq.index s i)})
                  (i':seq_index s{Some? (Seq.index s i') ∧ i ≠ i'})
  : Lemma (requires is_map_f s)
          (ensures VStoreE?.k (Some?.v (Seq.index s i)) ≠ VStoreE?.k (Some?.v (Seq.index s i')))
  = ()

type vstore = 
  | VStore: data:vstore_data -> is_map:bool{is_map ==> is_map_f data} -> vstore

let empty_store (n:nat) :vstore = VStore (Seq.create n None) true

let st_index (st:vstore) = seq_index st.data

let get_slot (st:vstore) (s:slot_id)
  : option vstore_entry
  = if s >= Seq.length st.data then None 
    else Seq.index st.data s

(* return true if s is a valid slot that is occupied *)
let store_contains (st:vstore) (s:slot_id) : bool
  = Some? (get_slot st s)

let store_contains_st_index (st:vstore) (s:slot_id{store_contains st s})
  : Lemma (s < Seq.length st.data)
          [SMTPat (store_contains st s)] 
  = ()

let lemma_store_contains_empty (n:nat) (s:slot_id)
  : Lemma (not (store_contains (empty_store n) s))
          [SMTPat (store_contains (empty_store n) s)]
  = ()

(* key stored at an occupied slot *)
let stored_key (st:vstore) (s:slot_id{store_contains st s}) : key
  = VStoreE?.k (Some?.v (get_slot st s))

let stored_value (st:vstore) (s:slot_id{store_contains st s}) : value
  = VStoreE?.v (Some?.v (get_slot st s))

let stored_value_matches_stored_key (st:vstore) (s:slot_id{store_contains st s}) 
  : Lemma (is_value_of (stored_key st s) (stored_value st s))
    [SMTPat (is_value_of (stored_key st s) (stored_value st s))]
  = ()

let add_method_of (st:vstore) (s:slot_id{store_contains st s}) : add_method
  = VStoreE?.am (Some?.v (get_slot st s))

let in_store_bit (st:vstore) (s:slot_id{store_contains st s}) (d:bin_tree_dir) : bool
  = match d with
    | Left -> VStoreE?.l_in_store (Some?.v (get_slot st s))
    | Right -> VStoreE?.r_in_store (Some?.v (get_slot st s))

let has_key (k:key) (e:option vstore_entry) : bool
  = match e with
    | Some (VStoreE k' _ _ _ _) -> k = k'
    | None -> false

(* if the store contains key k, return some entry in the store, otherwise return None *)
let lookup_key (st:vstore) (k:key) 
  : option vstore_entry
  = let s' = filter (has_key k) st.data in
    if Seq.length s' = 0 then None
    else Seq.index s' 0 

let store_contains_key (st:vstore) (k:key) : bool
  = Some? (lookup_key st k)

val lemma_store_contains_key (st:vstore) (k:key)
  : Lemma (requires (exists s. stored_key st s = k))
          (ensures (store_contains_key st k))
          [SMTPat (store_contains_key st k)]

val stored_value_by_key (st:vstore) (k:key{store_contains_key st k}) : value_type_of k

val add_method_of_by_key (st:vstore) (k:key{store_contains_key st k}) : add_method

(* Two cases where it's safe to add an entry (e) to the store (st) at slot s: 
   * e.k is not in st and s is empty
   * e.k is already at s *)
let compatible_entry (st:vstore) (s:st_index st) (e:vstore_entry) : Type
  = (not (store_contains st s) /\ not (store_contains_key st e.k)) \/ 
    (store_contains st s /\ stored_key st s = e.k) 

(* if the store is a map and it does not contain a e.k, then updating the store by adding e to 
    an empty slot is a map *)
val lemma_add_entry_case_1 (st:vstore) (s:st_index st) (e:vstore_entry)
  : Lemma (requires (st.is_map /\ not (store_contains st s) /\ not (store_contains_key st e.k)))
          (ensures (is_map_f (Seq.upd st.data s (Some e))))

(* if the store is a map and it contains e.k at slot s, then the store is a map after updating 
   slot s with e *)
val lemma_add_entry_case_2 (st:vstore) (s:st_index st) (e:vstore_entry)
  : Lemma (requires (st.is_map /\ store_contains st s /\ stored_key st s = e.k))
          (ensures (is_map_f (Seq.upd st.data s (Some e))))

let update_slot (st:vstore) (s:st_index st) (e:vstore_entry{compatible_entry st s e})
  : vstore
  = if st.is_map 
    then if not (store_contains_key st e.k) 
         then lemma_add_entry_case_1 st s e 
         else if store_contains st s && stored_key st s = e.k
              then lemma_add_entry_case_2 st s e;
    VStore (Seq.upd st.data s (Some e)) st.is_map

(* update the value of an occupied store slot with a compatible value *)
let update_value 
  (st:vstore)
  (s:slot_id{store_contains st s}) 
  (v:value_type_of (stored_key st s))
  : Tot (st':vstore {store_contains st' s /\
                     stored_value st' s = v})
  = let Some (VStoreE k _ am l r) = get_slot st s in
    update_slot st s (VStoreE k v am l r)

let update_value_preserves_length 
      (st:vstore) 
      (s:slot_id{store_contains st s}) 
      (v:value_type_of (stored_key st s)) 
  : Lemma (let st' = update_value st s v in
           Seq.length st.data = Seq.length st'.data)
          [SMTPat (Seq.length (VStore?.data (update_value st s v)))]  
  = ()

let lemma_update_value_preserves_is_map
      (st:vstore) 
      (s:slot_id{store_contains st s}) 
      (v:value_type_of (stored_key st s)) 
  : Lemma (let st' = update_value st s v in 
           st.is_map = st'.is_map)
          [SMTPat (VStore?.is_map (update_value st s v))]
  = ()

let lemma_update_value_preserves_slots
      (st:vstore) 
      (s:slot_id{store_contains st s}) 
      (v:value_type_of (stored_key st s))
      (s':slot_id)
  : Lemma (store_contains st s' = store_contains (update_value st s v) s')
          [SMTPat (store_contains (update_value st s v) s')]
  = ()

(* a key is present in a store iff it is present after updating 
   the store with a new value for some key at some slot *)
val lemma_update_value_preserves_keys
      (st:vstore) 
      (s:slot_id{store_contains st s}) 
      (v:value_type_of (stored_key st s))
      (k:key)
  : Lemma (store_contains_key st k = store_contains_key (update_value st s v) k)
          [SMTPat (store_contains_key (update_value st s v) k)]

(* update in-store bits *)
let update_in_store 
  (st:vstore)
  (s:slot_id{store_contains st s}) 
  (d:bin_tree_dir)
  (b:bool)
  : Tot (st':vstore {store_contains st' s /\
                     in_store_bit st' s d = b})
  = let Some (VStoreE k v am l r) = get_slot st s in
    match d with
    | Left -> update_slot st s (VStoreE k v am b r) 
    | Right -> update_slot st s (VStoreE k v am l b)

let lemma_update_in_store_preserves_is_map
      (st:vstore) 
      (s:slot_id{store_contains st s}) 
      (d:bin_tree_dir)
      (b:bool)
  : Lemma (let st' = update_in_store st s d b in 
           st.is_map = st'.is_map)
          [SMTPat (VStore?.is_map (update_in_store st s d b))]
  = ()

(* add a new entry (k,v,am) to the store at en empty slot s 
   if the store does not contain k, then preserve is_map; 
   otherwise set is_map to false *)
let add_to_store 
      (st:vstore) 
      (s:st_index st{not (store_contains st s)}) 
      (k:key) 
      (v:value_type_of k) 
      (am:add_method)
  : Tot (st':vstore {store_contains st' s /\
                     stored_key st' s = k /\
                     stored_value st' s = v /\
                     add_method_of st' s = am})
  = let e = VStoreE k v am false false in // default for in_store bits is false
    if not (store_contains_key st k)
    then update_slot st s e
    else VStore (Seq.upd st.data s (Some e)) false

let lemma_add_to_store_is_map1
      (st:vstore) 
      (s:st_index st) 
      (k:key) 
      (v:value_type_of k) 
      (am:add_method)
  : Lemma (requires (not (store_contains st s) /\ not (store_contains_key st k)))
          (ensures (let st' = add_to_store st s k v am in 
                    st.is_map = st'.is_map))
          [SMTPat (VStore?.is_map (add_to_store st s k v am))]
  = ()

(* is_map is false when adding a duplicate key *)
let lemma_add_to_store_is_map2
      (st:vstore) 
      (s:st_index st) 
      (k:key) 
      (v:value_type_of k) 
      (am:add_method)
  : Lemma (requires (not (store_contains st s) /\ store_contains_key st k))
          (ensures (let st' = add_to_store st s k v am in 
                    st'.is_map = false))
          [SMTPat (VStore?.is_map (add_to_store st s k v am))]
  = ()

(* remove an entry from a slot; reset slot to unused *)
let evict_from_store (st:vstore) (s:st_index st)
  : Tot (st':vstore {not (store_contains st' s)})
  = VStore (Seq.upd st.data s None) st.is_map

let lemma_evict_from_store_preserves_is_map (st:vstore) (s:st_index st)
  : Lemma (st.is_map = VStore?.is_map (evict_from_store st s))
          [SMTPat (VStore?.is_map (evict_from_store st s))]
  = ()

(* slot_id s is equivalent to key k *)
let slot_key_equiv (st:vstore) (s:slot_id) (k:key) : bool =
  not st.is_map || // trivially true
  (store_contains st s && stored_key st s = k) 

(* if s contains k, it continues to contain k after an unrelated update *)
val lemma_slot_key_equiv_update_value 
      (st:vstore) 
      (s:slot_id) 
      (s':slot_id{store_contains st s'}) 
      (k:key) 
      (v:value_type_of (stored_key st s'))
  : Lemma (requires (slot_key_equiv st s k /\ s <> s'))
          (ensures (slot_key_equiv (update_value st s' v) s k))
          [SMTPat (slot_key_equiv (update_value st s' v) s k)]

(* convert a slot-indexed store to a key-indexed store *)
val as_map (st:vstore{st.is_map}) : Spec.vstore

val lemma_as_map_empty (n:nat) 
  : Lemma (ensures (let st = empty_store n in
                     forall (k:key). as_map st k = None))
          (decreases n)

val lemma_as_map_slot_key_equiv (st:vstore{st.is_map}) (s:slot_id) (k:key)
  : Lemma (requires (slot_key_equiv st s k)) 
          (ensures (Spec.store_contains (as_map st) k /\
                    stored_value st s = Spec.stored_value (as_map st) k /\
                    add_method_of st s = Spec.add_method_of (as_map st) k))
          [SMTPat (slot_key_equiv st s k)]

(* Relation between stores *)
let store_rel (st:vstore) (st':Spec.vstore) : Type = 
  st.is_map /\ FE.feq st' (as_map st)

val lemma_store_rel_contains_key (st:vstore) (st':Spec.vstore) (k:key)
  : Lemma (requires (store_rel st st'))
          (ensures (store_contains_key st k = Spec.store_contains st' k))
          [SMTPat (store_contains_key st k); SMTPat (Spec.store_contains st' k)]

val lemma_store_rel_stored_value (st:vstore) (st':Spec.vstore) (k:key)
  : Lemma (requires (store_rel st st' /\ store_contains_key st k))
          (ensures (stored_value_by_key st k = Spec.stored_value st' k))
          [SMTPat (stored_value_by_key st k); SMTPat (Spec.stored_value st' k)]

val lemma_store_rel_add_method_of (st:vstore) (st':Spec.vstore) (k:key)
  : Lemma (requires (store_rel st st' /\ store_contains_key st k))
          (ensures (add_method_of_by_key st k = Spec.add_method_of st' k))
          [SMTPat (add_method_of_by_key st k); SMTPat (Spec.add_method_of st' k)]

val lemma_store_rel_update_value (st:vstore) (st':Spec.vstore) (s:slot_id) (k:key) (v:value_type_of k)
  : Lemma (requires (store_rel st st' /\ slot_key_equiv st s k))
          (ensures (store_rel (update_value st s v) (Spec.update_store st' k v)))
          [SMTPat (update_value st s v); SMTPat (Spec.update_store st' k v)]

val lemma_store_rel_update_in_store (st:vstore) (st':Spec.vstore) (s:slot_id) (d:bin_tree_dir) (b:bool)
  : Lemma (requires (store_rel st st' /\ store_contains st s))
          (ensures (store_rel (update_in_store st s d b) st'))
          [SMTPat (store_rel (update_in_store st s d b) st')]

val lemma_store_rel_add_to_store (st:vstore) (st':Spec.vstore) (s:st_index st) (k:key) (v:value_type_of k) (am:add_method)
  : Lemma (requires (store_rel st st' /\ not (store_contains st s) /\ not (Spec.store_contains st' k)))
          (ensures (store_rel (add_to_store st s k v am) (Spec.add_to_store st' k v am)))
          [SMTPat (add_to_store st s k v am); SMTPat (Spec.add_to_store st' k v am)]

val lemma_store_rel_evict_from_store (st:vstore) (st':Spec.vstore) (s:st_index st) (k:key)
  : Lemma (requires (store_rel st st' /\ slot_key_equiv st s k))
          (ensures (store_rel (evict_from_store st s) (Spec.evict_from_store st' k)))
          [SMTPat (evict_from_store st s); SMTPat (Spec.evict_from_store st' k)]




let store_contains_merkle_slot (st:vstore) (s:slot_id) : bool
  = store_contains st s && MVal? (stored_value st s)

type instore_merkle_slot (st:vstore) = s:slot_id{store_contains_merkle_slot st s}

let store_contains_key_with_MAdd (st:vstore) (k:key) : bool
  = store_contains_key st k && add_method_of_by_key st k = Spec.MAdd

let lemma_update_value_preserves_key_with_MAdd
  (st:vstore)
  (s:slot_id{store_contains st s}) 
  (v:value_type_of (stored_key st s))
  (k:key)
  : Lemma (ensures store_contains_key_with_MAdd st k = 
                     store_contains_key_with_MAdd (update_value st s v) k)
          [SMTPat (store_contains_key_with_MAdd (update_value st s v) k)]
  = admit()
     
let lemma_add_to_store_BAdd_preserves_key_with_MAdd
  (st:vstore)
  (s:st_index st{not (store_contains st s)}) 
  (k:key)
  (v:value_type_of k)
  (k0:key)
  : Lemma (ensures store_contains_key_with_MAdd st k0 = 
                     store_contains_key_with_MAdd (add_to_store st s k v Spec.BAdd) k0)
          [SMTPat (store_contains_key_with_MAdd (add_to_store st s k v Spec.BAdd) k0)]
  = admit()    

let lemma_add_to_store_MAdd_preserves_key_with_MAdd
  (st:vstore)
  (s:st_index st{not (store_contains st s)}) 
  (k:key)
  (v:value_type_of k)
  (k0:key)
  : Lemma (requires k <> k0)
          (ensures store_contains_key_with_MAdd st k0 =
                     store_contains_key_with_MAdd (add_to_store st s k v Spec.MAdd) k0)
          [SMTPat (store_contains_key_with_MAdd (add_to_store st s k v Spec.MAdd) k0)]
  = admit()    

let lemma_add_to_store_adds_key_with_MAdd
  (st:vstore)
  (s:st_index st{not (store_contains st s)}) 
  (k:key)
  (v:value_type_of k)
  : Lemma (ensures store_contains_key_with_MAdd (add_to_store st s k v Spec.MAdd) k)
          [SMTPat (store_contains_key_with_MAdd (add_to_store st s k v Spec.MAdd) k)]
  = admit()    


let lemma_update_in_store_preserves_in_store_bit
      (st:vstore)
      (s:slot_id{store_contains st s})
      (d:bin_tree_dir)
      (b:bool)
      (s0:slot_id{store_contains st s0})
      (d0:bin_tree_dir)
  : Lemma (requires s0 <> s)
          (ensures in_store_bit st s0 d0 = in_store_bit (update_in_store st s d b) s0 d0)
          [SMTPat (in_store_bit (update_in_store st s d b) s0 d0)]
  = ()

let lemma_update_in_store_updates_in_store_bit
      (st:vstore)
      (s:slot_id{store_contains st s})
      (d:bin_tree_dir)
      (b:bool)
  : Lemma (ensures in_store_bit (update_in_store st s d b) s d = b)
          [SMTPat (in_store_bit (update_in_store st s d b) s d)]
  = ()

let lemma_update_in_store_preserves_keys
  (st:vstore)
  (s:st_index st{store_contains st s}) 
  (d:bin_tree_dir)
  (b:bool)
  (k:key)
  : Lemma (ensures store_contains_key st k = store_contains_key (update_in_store st s d b) k)
          [SMTPat (store_contains_key (update_in_store st s d b) k)]
  = admit()

let lemma_update_in_store_preserves_add_method
  (st:vstore)
  (s:st_index st{store_contains st s}) 
  (d:bin_tree_dir)
  (b:bool)
  (k:key{store_contains_key st k})
  : Lemma (ensures add_method_of_by_key st k = add_method_of_by_key (update_in_store st s d b) k)
          [SMTPat (add_method_of_by_key (update_in_store st s d b) k)]
  = admit()

let lemma_update_in_store_preserves_key_with_MAdd
  (st:vstore)
  (s:st_index st{store_contains st s}) 
  (d:bin_tree_dir)
  (b:bool)
  (k:key)
  : Lemma (ensures store_contains_key_with_MAdd st k = 
                     store_contains_key_with_MAdd (update_in_store st s d b) k)
          [SMTPat (store_contains_key_with_MAdd (update_in_store st s d b) k)]
  = ()

let lemma_evict_from_store_evicts_key
  (st:vstore{st.is_map})
  (s:st_index st{store_contains st s}) 
  : Lemma (ensures not (store_contains_key (evict_from_store st s) (stored_key st s)))
          [SMTPat (store_contains_key (evict_from_store st s) (stored_key st s))]
  = admit()    

let lemma_evict_from_store_preserves_key_with_MAdd
  (st:vstore{st.is_map})
  (s:st_index st{store_contains st s}) 
  (k:key)
  : Lemma (requires (k <> stored_key st s))
          (ensures (store_contains_key_with_MAdd st k = store_contains_key_with_MAdd (evict_from_store st s) k))
          [SMTPat (store_contains_key_with_MAdd (evict_from_store st s) k)]
  = admit()    

let lemma_evict_from_store_BAdd_preserves_key_with_MAdd
  (st:vstore{st.is_map})
  (s:st_index st{store_contains st s}) 
  (k:key)
  : Lemma (requires (add_method_of st s = Spec.BAdd))
          (ensures (store_contains_key_with_MAdd st k = store_contains_key_with_MAdd (evict_from_store st s) k))
          [SMTPat (store_contains_key_with_MAdd (evict_from_store st s) k)]
  = admit()    
