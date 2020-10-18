module Veritas.Intermediate.StoreSKC

open Veritas.Key
open Veritas.Record
open Veritas.SeqAux

module Spec = Veritas.Verifier

let slot_id = nat
let add_method = Veritas.Verifier.add_method

type vstore_entry = 
  | VStore: k:key -> v:value_type_of k -> am:add_method -> vstore_entry

type vstore = {
  data:Seq.seq (option vstore_entry);
  is_map:bool;
}

let st_index (st:vstore) = seq_index st.data

val store_contains (st:vstore) (s:slot_id) : bool

val store_contains_st_index (st:vstore) (s:slot_id{store_contains st s})
  : Lemma (s < Seq.length st.data)
          [SMTPat (store_contains st s)] 

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

val add_to_store 
      (st:vstore) 
      (s:st_index st) 
      (k:key) 
      (v:value_type_of k) 
      (am:add_method)
  : Tot (st':vstore {store_contains st' s /\
                     stored_key st' s = k /\
                     stored_value st' s = v /\
                     add_method_of st' s = am})

val evict_from_store (st:vstore) (s:st_index st)
  : Tot (st':vstore {not (store_contains st' s)})

(* slot_id s is equivalent to key k *)
let slot_key_equiv (st:vstore) (s:slot_id) (k:key) : bool =
  not st.is_map || // trivially true
  (store_contains st s && stored_key st s = k) 

(* convert a slot-indexed store to a key-indexed store *)
val as_map (st:vstore{st.is_map}) : Spec.vstore

val lemma_as_map_slot_key_equiv (st:vstore{st.is_map}) (s:slot_id) (k:key)
  : Lemma (requires (slot_key_equiv st s k)) 
          (ensures (Spec.store_contains (as_map st) k /\
                    stored_value st s = Spec.stored_value (as_map st) k))
