module Veritas.Intermediate.StoreSKC

open Veritas.Key
open Veritas.Record
open Veritas.SeqAux

module Spec = Veritas.Verifier
module FE = FStar.FunctionalExtensionality

let slot_id = nat
let add_method = Veritas.Verifier.add_method

type vstore_entry = 
  | VStoreE: k:key -> v:value_type_of k -> am:add_method -> vstore_entry

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

val store_contains (st:vstore) (s:slot_id) : bool

val store_contains_st_index (st:vstore) (s:slot_id{store_contains st s})
  : Lemma (s < Seq.length st.data)
          [SMTPat (store_contains st s)] 

val lemma_store_contains_empty (n:nat) (s:slot_id)
  : Lemma (not (store_contains (empty_store n) s))
          [SMTPat (store_contains (empty_store n) s)]

val stored_key (st:vstore) (s:slot_id{store_contains st s}) : key

val stored_value (st:vstore) (s:slot_id{store_contains st s}) : value

val stored_value_matches_stored_key (st:vstore) (s:slot_id{store_contains st s}) 
  : Lemma (is_value_of (stored_key st s) (stored_value st s))
    [SMTPat (is_value_of (stored_key st s) (stored_value st s))]

val add_method_of (st:vstore) (s:slot_id{store_contains st s}) : add_method

val store_contains_key (st:vstore) (k:key) : bool

val lemma_store_contains_key (st:vstore) (k:key)
  : Lemma (requires (exists s. stored_key st s = k))
          (ensures (store_contains_key st k))
          [SMTPat (store_contains_key st k)]

val stored_value_by_key (st:vstore) (k:key{store_contains_key st k}) : value_type_of k

val add_method_of_by_key (st:vstore) (k:key{store_contains_key st k}) : add_method

val update_store 
      (st:vstore) 
      (s:slot_id{store_contains st s}) 
      (v:value_type_of (stored_key st s))
  : Tot (st':vstore {store_contains st' s /\
                     stored_value st' s = v})

val update_store_preserves_length 
      (st:vstore) 
      (s:slot_id{store_contains st s}) 
      (v:value_type_of (stored_key st s)) 
  : Lemma (let st' = update_store st s v in
           Seq.length st.data = Seq.length st'.data)
          [SMTPat (update_store st s v)]  

val lemma_update_store_preserves_is_map
      (st:vstore) 
      (s:slot_id{store_contains st s}) 
      (v:value_type_of (stored_key st s)) 
  : Lemma (let st' = update_store st s v in 
           st.is_map = st'.is_map)
          [SMTPat (update_store st s v)]

val lemma_update_store_preserves_slots
      (st:vstore) 
      (s:slot_id{store_contains st s}) 
      (v:value_type_of (stored_key st s))
  : Lemma (let st' = update_store st s v in
           forall s. store_contains st s = store_contains st' s)
          [SMTPat (update_store st s v)]

val add_to_store 
      (st:vstore) 
      (s:st_index st{not (store_contains st s)})
      (k:key) 
      (v:value_type_of k) 
      (am:add_method)
  : Tot (st':vstore {store_contains st' s /\
                     stored_key st' s = k /\
                     stored_value st' s = v /\
                     add_method_of st' s = am})

val lemma_add_to_store_is_map1
      (st:vstore) 
      (s:st_index st) 
      (k:key) 
      (v:value_type_of k) 
      (am:add_method)
  : Lemma (requires (not (store_contains st s) /\ not (store_contains_key st k)))
          (ensures (let st' = add_to_store st s k v am in 
                    st.is_map = st'.is_map))
          [SMTPat (add_to_store st s k v am)]

val lemma_add_to_store_is_map2
      (st:vstore) 
      (s:st_index st) 
      (k:key) 
      (v:value_type_of k) 
      (am:add_method)
  : Lemma (requires (not (store_contains st s) /\ store_contains_key st k))
          (ensures (let st' = add_to_store st s k v am in 
                    st'.is_map = false))
          [SMTPat (add_to_store st s k v am)]

val evict_from_store (st:vstore) (s:st_index st)
  : Tot (st':vstore {not (store_contains st' s)})

val lemma_evict_from_store_preserves_is_map (st:vstore) (s:st_index st)
  : Lemma (let st' = evict_from_store st s in
           st.is_map = st'.is_map)
          [SMTPat (evict_from_store st s)]

(* slot_id s is equivalent to key k *)
let slot_key_equiv (st:vstore) (s:slot_id) (k:key) : bool =
  not st.is_map || // trivially true
  (store_contains st s && stored_key st s = k) 

val lemma_slot_key_equiv_update_store 
      (st:vstore) 
      (s:slot_id) 
      (s':slot_id{store_contains st s'}) 
      (k:key) 
      (v:value_type_of (stored_key st s'))
  : Lemma (requires (slot_key_equiv st s k /\ s <> s'))
          (ensures (slot_key_equiv (update_store st s' v) s k))
          [SMTPat (slot_key_equiv (update_store st s' v) s k)]

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

val lemma_store_rel_update_store (st:vstore) (st':Spec.vstore) (s:slot_id) (k:key) (v:value_type_of k)
  : Lemma (requires (store_rel st st' /\ slot_key_equiv st s k))
          (ensures (store_rel (update_store st s v) (Spec.update_store st' k v)))
          [SMTPat (update_store st s v); SMTPat (Spec.update_store st' k v)]

val lemma_store_rel_add_to_store (st:vstore) (st':Spec.vstore) (s:st_index st) (k:key) (v:value_type_of k) (am:add_method)
  : Lemma (requires (store_rel st st' /\ not (store_contains st s) /\ not (Spec.store_contains st' k)))
          (ensures (store_rel (add_to_store st s k v am) (Spec.add_to_store st' k v am)))
          [SMTPat (add_to_store st s k v am); SMTPat (Spec.add_to_store st' k v am)]

val lemma_store_rel_evict_from_store (st:vstore) (st':Spec.vstore) (s:st_index st) (k:key)
  : Lemma (requires (store_rel st st' /\ slot_key_equiv st s k))
          (ensures (store_rel (evict_from_store st s) (Spec.evict_from_store st' k)))
          [SMTPat (evict_from_store st s); SMTPat (Spec.evict_from_store st' k)]
