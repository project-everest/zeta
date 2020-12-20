module Veritas.Intermediate.Store

open Veritas.BinTree
open Veritas.Key
open Veritas.Record
open Veritas.SeqAux

module Spec = Veritas.Verifier
module FE = FStar.FunctionalExtensionality

(*** General Definitions & Basic Facts ***)

let add_method = Veritas.Verifier.add_method

(* 
 * vstore_entry - reflect a Spec.vstore_entry with two additional fields tracking 
 * whether a left/right descendant was added using merkle using this slot as "proof"
 *)
type vstore_entry = 
  | VStoreE: k:key -> 
             v:value_type_of k -> 
             am:add_method -> 
             l_in_store : option nat{is_merkle_key k \/ None = l_in_store} -> 
             r_in_store : option nat{is_merkle_key k \/ None = r_in_store} -> 
             vstore_entry

(* vstore_raw: the raw version of the vstore; the actual vstore 
 * is the raw version with some invariants *)
type vstore_raw = Seq.seq (option vstore_entry) 

(* an index in store *)
let slot_id (st:vstore_raw) = seq_index st

let get_slot (st:vstore_raw) (s: slot_id st)
  : option vstore_entry
  = Seq.index st s

(* return true if s is a valid slot that is occupied *)
let inuse_slot (st:vstore_raw) (s:slot_id st) : bool
  = Some? (get_slot st s)

(* dep type of all slots in use *)
let inuse_slot_id (st: vstore_raw) = s:slot_id st{inuse_slot st s}

let get_inuse_slot (st:vstore_raw) (s:inuse_slot_id st) =
  Some?.v (get_slot st s)

(* is this an empty slot *)
let empty_slot (st:vstore_raw) (s:slot_id st): bool 
  = None = get_slot st s

let empty_slot_id (st: vstore_raw) = s:slot_id st{empty_slot st s}

(* key stored at an occupied slot *)
let stored_key (st:vstore_raw) (s:inuse_slot_id st) : key
  = VStoreE?.k (Some?.v (get_slot st s))

(* is this a slot containing a merkle key *)
let merkle_slot_id (st:vstore_raw)
  = s:inuse_slot_id st{is_merkle_key (stored_key st s)}

let data_slot_id (st:vstore_raw)
  = s:inuse_slot_id st{is_data_key (stored_key st s)}

let stored_value (st:vstore_raw) (s:inuse_slot_id st) : value
  = VStoreE?.v (Some?.v (get_slot st s))

let add_method_of (st:vstore_raw) (s:inuse_slot_id st) : add_method
  = VStoreE?.am (Some?.v (get_slot st s))

(* TODO: Move to a better place ?*)
let mv_points_to_none (mv:merkle_value) (d:bin_tree_dir): bool 
  = Empty? (desc_hash_dir mv d)

let mv_points_to_some (mv:merkle_value) (d:bin_tree_dir) : bool
  = Desc? (desc_hash_dir mv d)

let mv_pointed_key (mv:merkle_value) (d:bin_tree_dir{mv_points_to_some mv d}) : key
  = Desc?.k (desc_hash_dir mv d)

(* was a descendant added with MAdd along direction d *)
let desc_in_store (st:vstore_raw) (s:inuse_slot_id st) (d:bin_tree_dir) : bool
  = match d with
    | Left -> Some? (VStoreE?.l_in_store (Some?.v (get_slot st s)))
    | Right -> Some? (VStoreE?.r_in_store (Some?.v (get_slot st s)))

(* if a descendant was added with MAdd, the slot where the descendant was added *)
let desc_slot_raw (st:vstore_raw) (s:inuse_slot_id st) (d:bin_tree_dir{desc_in_store st s d}): nat
  = match d with
    | Left -> Some?.v (VStoreE?.l_in_store (Some?.v (get_slot st s)))
    | Right -> Some?.v (VStoreE?.r_in_store (Some?.v (get_slot st s)))

(* invariant connecting the value stored in a slot and the desc info *)
let desc_in_store_inv_merkle (st:vstore_raw) (s:merkle_slot_id st) (d:bin_tree_dir) = 
  let v = to_merkle_value (stored_value st s) in
  mv_points_to_none v d /\ not (desc_in_store st s d) \/
  mv_points_to_some v d /\ (desc_in_store st s d ==> 
                            (let ds = desc_slot_raw st s d in
                             ds < Seq.length st /\               // valid slot_id                 
                             (let dk = mv_pointed_key v d in
                              inuse_slot st ds /\                // slot_id in use                              
                              stored_key st ds = dk /\           // stored key is the key in my value
                              add_method_of st ds = Spec.MAdd))) // Merkle add

let desc_in_store_inv_data (st:vstore_raw) (s:data_slot_id st) = 
  not (desc_in_store st s Left) && 
  not (desc_in_store st s Right)

let store_inv_slot (st:vstore_raw) (s:slot_id st) = 
  empty_slot st s \/
  (is_data_key (stored_key st s) /\ desc_in_store_inv_data st s) \/
  (is_merkle_key (stored_key st s) /\ 
   desc_in_store_inv_merkle st s Left /\ 
   desc_in_store_inv_merkle st s Right)

let store_inv_local (st:vstore_raw) = 
  forall (s:slot_id st). store_inv_slot st s

let vstore = st:vstore_raw{store_inv_local st}

let empty_store (n:nat) :vstore = Seq.create n None
  
let has_key (k:key) (e:option vstore_entry) : bool
  = match e with
    | Some (VStoreE k' _ _ _ _) -> k = k'
    | None -> false

(* desc slot verified version that returns a slot id *)
let desc_slot (st:vstore) 
              (s:merkle_slot_id st) 
              (d:bin_tree_dir{desc_in_store st s d}): slot_id st = 
  desc_slot_raw st s d

(** vstore update methods **)

(* relationship between two stores st and st' that states that 
 * they are of the same size and differ in only one slot *)
let idx_store_update_rel (st st': vstore) (s:slot_id st) 
  = Seq.length st = Seq.length st' /\
    (forall (s':slot_id st). (s' <> s ==> get_slot st s' == get_slot st' s'))

(* add a new entry (k,v) to the store at en empty slot s; *)
val add_to_store 
      (st:vstore) 
      (s:empty_slot_id st)
      (k:key) 
      (v:value_type_of k) 
      (am:add_method)
  : Tot (st':vstore {idx_store_update_rel st st' s /\
                     inuse_slot st' s /\
                     get_inuse_slot st' s = VStoreE k v am None None})

(* add a new entry with merkle and a descendant *)
(* TODO: Add when this is used *)
val add_to_store_with_desc
      (st:vstore)
      (s:empty_slot_id st)
      (k:merkle_key)
      (v:merkle_value)
      (d:bin_tree_dir{mv_points_to_some v d})
      (s':merkle_slot_id st{mv_pointed_key v d = stored_key st s'})
  : Tot (st':vstore {idx_store_update_rel st st' s /\
                     inuse_slot st' s /\
                     stored_key st' s = k /\
                     stored_value st' s = (MVal v) /\
                     add_method_of st' s = Spec.MAdd /\
                     desc_in_store st' s d /\
                     desc_slot st' s d = s' /\
                     not (desc_in_store st' s d)})
                     
(* update the data value of a data key *)
val update_data_value 
  (st:vstore)
  (s:data_slot_id st)
  (v:data_value)
  : Tot (st':vstore {
        let VStoreE k _ am _ _ = get_inuse_slot st s in
        (idx_store_update_rel st st' s /\
         inuse_slot st' s /\
         get_inuse_slot st' s = VStoreE k (DVal v) am None None)})

(* reset a descendant of a merkle slot *)
val reset_desc_slot
  (st:vstore)
  (s:merkle_slot_id st)
  (d:bin_tree_dir{desc_in_store st s d})
  : Tot (st': vstore {idx_store_update_rel st st' s /\
                      inuse_slot st' s /\ 
                      stored_key st' s = stored_key st s /\
                      not (desc_in_store st s d)})

(* two values point to the same key along some dir (or don't point to any) *)
let points_to_same (v1 v2: merkle_value) (d:bin_tree_dir) = 
  mv_points_to_none v1 d && mv_points_to_none v2 d ||
  mv_points_to_some v1 d && mv_points_to_some v2 d && 
  mv_pointed_key v1 d = mv_pointed_key v2 d

(* update a merkle value with a new value that points to the same keys *)
val update_merkle_value
  (st:vstore)
  (s:merkle_slot_id st)
  (v:merkle_value {let vold = to_merkle_value (stored_value st s) in
                   points_to_same v vold Left &&
                   points_to_same v vold Right})
  : Tot (st': vstore {idx_store_update_rel st st' s /\
                      inuse_slot st' s /\
                      (let VStoreE k _ am ld rd = get_inuse_slot st s in
                       get_inuse_slot st' s = VStoreE k (MVal v) am ld rd)})

(* remove an entry from a slot; reset slot to unused *)
val evict_from_store (st:vstore) (s:inuse_slot_id st)
  : Tot (st':vstore {idx_store_update_rel st st' s /\
                     empty_slot st' s})

(* if the store contains key k, return some entry in the store, otherwise return None *)
let lookup_key (st:vstore) (k:key) 
  : option vstore_entry
  = let s' = filter (has_key k) st in
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

(*** Store Invariants ***)

(* In our correctness proof, we will want to maintain two invariants over stores:
   * is_map: there are no duplicate keys in the store, so there is a 1-to-1 mapping
     between the slot-based store and a standard key-value map
   * in_store_inv: the "desc_in_store" accurately reflect which the desc invariant
*)

(* No duplicate keys in the store *)
let is_map (st:vstore) =
  forall (s:inuse_slot_id st) 
    (s':inuse_slot_id st{s' <> s}). 
        // TODO: this pattern is pretty general -- it may lead to proof performance issues
        {:pattern (Seq.index st s); (Seq.index st s')} 
    stored_key st s <> stored_key st s'

let elim_is_map (st:vstore) 
                (s:inuse_slot_id st)
                (s':inuse_slot_id st{s' <> s})
  : Lemma (requires is_map st)
          (ensures stored_key st s ≠ stored_key st s')
  = ()

(* a store that is a map *)
let ismap_vstore = st:vstore{is_map st}

(* updating a data value preserves is_map *)
val lemma_update_data_value_preserves_is_map
      (st:ismap_vstore)
      (s:data_slot_id st)
      (v:data_value)
  : Lemma (ensures (is_map (update_data_value st s v)))
          [SMTPat (update_data_value st s v)]

(* reset desc slot preserves is_map *)
val lemma_reset_desc_slot_preserves_is_map
      (st:ismap_vstore)
      (s:merkle_slot_id st)
      (d:bin_tree_dir{desc_in_store st s d})
  : Lemma (ensures (is_map (reset_desc_slot st s d)))
          [SMTPat (is_map (reset_desc_slot st s d))]

val lemma_update_merkle_value
      (st:ismap_vstore)
      (s:merkle_slot_id st)
      (v:merkle_value {let vold = to_merkle_value (stored_value st s) in
                       points_to_same v vold Left &&
                       points_to_same v vold Right})
  : Lemma (ensures (is_map (update_merkle_value st s v)))
          [SMTPat (is_map (update_merkle_value st s v))]

(* is_map is preserved when adding a new key *)
val lemma_add_to_store_is_map1
      (st:ismap_vstore) 
      (s:empty_slot_id st) 
      (k:key{not (store_contains_key st k)}) 
      (v:value_type_of k) 
      (am:add_method)
  : Lemma (ensures (is_map (add_to_store st s k v am)))
          [SMTPat (is_map (add_to_store st s k v am))]

(* is_map is violated when adding a duplicate key *)
val lemma_add_to_store_is_map2
      (st:vstore) 
      (s:empty_slot_id st) 
      (k:key{store_contains_key st k}) 
      (v:value_type_of k) 
      (am:add_method)
  : Lemma (ensures (~ (is_map (add_to_store st s k v am))))
          [SMTPat (is_map (add_to_store st s k v am))]

val lemma_evict_from_store_preserves_is_map (st:ismap_vstore) (s:inuse_slot_id st)
  : Lemma (ensures (is_map (evict_from_store st s)))
          [SMTPat (is_map (evict_from_store st s))]

(*** Relation w/ Spec-level Stores ***)

(* slot_id s is equivalent to key k *)
let slot_key_equiv (st:vstore) (s:slot_id st) (k:key) : bool =
  inuse_slot st s && stored_key st s = k 

(*
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
*)

(* convert a slot-indexed store to a key-indexed store *)
val as_map (st:ismap_vstore) : Spec.vstore

val lemma_as_map_empty (n:nat) 
  : Lemma (ensures (let st = empty_store n in
                     forall (k:key). as_map st k = None))
          (decreases n)

val lemma_as_map_slot_key_equiv (st:ismap_vstore) (s:slot_id st) (k:key)
  : Lemma (requires (slot_key_equiv st s k)) 
          (ensures (Spec.store_contains (as_map st) k /\
                    stored_value st s = Spec.stored_value (as_map st) k /\
                    add_method_of st s = Spec.add_method_of (as_map st) k))
          [SMTPat (slot_key_equiv st s k)]

(* Relation between stores *)
let store_rel (st:vstore) (st':Spec.vstore) : Type = 
  is_map st /\ FE.feq st' (as_map st)

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

(*
val lemma_store_rel_update_value (st:vstore) (st':Spec.vstore) (s:slot_id) (k:key) (v:value_type_of k)
  : Lemma (requires (store_rel st st' /\ slot_key_equiv st s k))
          (ensures (store_rel (update_value st s v) (Spec.update_store st' k v)))
          [SMTPat (update_value st s v); SMTPat (Spec.update_store st' k v)]

val lemma_store_rel_update_in_store (st:vstore) (st':Spec.vstore) (s:slot_id) (d:bin_tree_dir) (b:bool)
  : Lemma (requires (store_rel st st' /\ store_contains st s))
          (ensures (store_rel (update_in_store st s d b) st'))
          [SMTPat (store_rel (update_in_store st s d b) st')]
*)

val lemma_store_rel_add_to_store 
      (st:vstore) 
      (st':Spec.vstore) 
      (s:empty_slot_id st) 
      (k:key) 
      (v:value_type_of k) 
      (am:add_method)
  : Lemma (requires (store_rel st st' /\ not (Spec.store_contains st' k)))
          (ensures (store_rel (add_to_store st s k v am) (Spec.add_to_store st' k v am)))
          [SMTPat (add_to_store st s k v am); SMTPat (Spec.add_to_store st' k v am)]

val lemma_store_rel_evict_from_store (st:vstore) (st':Spec.vstore) (s:slot_id st) (k:key)
  : Lemma (requires (store_rel st st' /\ slot_key_equiv st s k))
          (ensures (store_rel (evict_from_store st s) (Spec.evict_from_store st' k)))
          [SMTPat (evict_from_store st s); SMTPat (Spec.evict_from_store st' k)]
