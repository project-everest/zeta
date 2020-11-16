module Veritas.Intermediate.StoreS

open Veritas.BinTree
open Veritas.Key
open Veritas.Record
open Veritas.SeqAux

module Spec = Veritas.Verifier
module SC = Veritas.Intermediate.StoreSC

let slot_id = nat
let add_method = Spec.add_method

type vstore_entry = 
  | VStoreE: k:key -> 
             v:value_type_of k -> 
             am:add_method -> 
             l_child_in_store:bool ->
             r_child_in_store:bool ->
             vstore_entry

type vstore = Seq.seq (option vstore_entry) 

let empty_store (n:nat) :vstore = Seq.create n None

let st_index (st:vstore) = seq_index st

val store_contains (st:vstore) (s:slot_id) : bool

val stored_key (st:vstore) (s:slot_id{store_contains st s}) : key

val stored_value (st:vstore) (s:slot_id{store_contains st s}) : value

val add_method_of (st:vstore) (s:slot_id{store_contains st s}) : add_method

val l_child_in_store (st:vstore) (s:slot_id{store_contains st s}) : bool

val r_child_in_store (st:vstore) (s:slot_id{store_contains st s}) : bool

val store_contains_key (st:vstore) (k:key) : bool

val stored_value_by_key (st:vstore) (k:key{store_contains_key st k}) : value_type_of k

val add_method_of_by_key (st:vstore) (k:key{store_contains_key st k}) : add_method

val update_value 
      (st:vstore) 
      (s:slot_id{store_contains st s}) 
      (v:value_type_of (stored_key st s))
  : Tot (st':vstore {store_contains st' s /\ stored_value st' s = v})

val update_in_store 
  (st:vstore)
  (s:slot_id{store_contains st s}) 
  (d:bin_tree_dir)
  (b:bool)
  : Tot (st':vstore {store_contains st' s /\
                     (match d with
                      | Left -> l_child_in_store st' s = b
                      | Right -> r_child_in_store st' s = b)})

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

val evict_from_store 
      (st:vstore) 
      (s:slot_id{store_contains st s})
  : Tot (st':vstore {not (store_contains st' s)})

(* How to check that a key is not in the store with add_method=MAdd:
   1. If a child_in_store flag is unset then the corresponding descendent is not in the store.
   2. k' point to the nearest descendent in the store.
      (a) If k' points to k2 then no key between k' and k2 is in the store.
      (b) If k' points to Empty then no descendent of k' in that direction is in the store.
      
   How to check that a key is not in the store with add_method=BAdd PROVIDED that the add/evict 
   set hashes have not diverged:
   1, If the evicted_to_blum flag is unset then the corresponding descendent is not in the store. 
   2. Same as above. *)
let store_contains_key_with_am (st:vstore) (k:key) (am:add_method) : bool
  = store_contains_key st k && add_method_of_by_key st k = am

let in_store_flag_unset_implies_desc_not_in_store
      (st:vstore)
      (s:slot_id{store_contains st s /\ MVal? (stored_value st s)})
  = let v = to_merkle_value (stored_value st s) in    
    let ld = desc_hash_dir v Left in
    let rd = desc_hash_dir v Right in
    (Desc? ld /\ not (l_child_in_store st s) ==>
       not (store_contains_key_with_am st (Desc?.k ld) Spec.MAdd)) /\
    (Desc? rd /\ not (r_child_in_store st s) ==> 
       not (store_contains_key_with_am st (Desc?.k rd) Spec.MAdd))

let evicted_to_blum_flag_unset_implies_desc_not_in_store
      (st:vstore)
      (s:slot_id{store_contains st s /\ MVal? (stored_value st s)})
  = let v = to_merkle_value (stored_value st s) in    
    let ld = desc_hash_dir v Left in
    let rd = desc_hash_dir v Right in
    (Desc? ld /\ not (Desc?.b ld) ==>
       not (store_contains_key_with_am st (Desc?.k ld) Spec.BAdd)) /\
    (Desc? rd /\ not (Desc?.b rd) ==> 
       not (store_contains_key_with_am st (Desc?.k rd) Spec.BAdd))

let points_to_nearest_desc_in_store 
      (st:vstore)
      (s:slot_id{store_contains st s /\ MVal? (stored_value st s)})
      (am:add_method)
  = let k' = stored_key st s in
    let v' = to_merkle_value (stored_value st s) in
    forall (k:key{is_proper_desc k k'}).
    let dh = desc_hash_dir v' (desc_dir k k') in
    if Empty? dh then not (store_contains_key_with_am st k am)
    else if is_proper_desc (Desc?.k dh) k then not (store_contains_key_with_am st k am) 
    else True

// always true by the structure of vaddm
let merkle_store_inv (st:vstore) = 
  forall (s:slot_id{store_contains st s /\ MVal? (stored_value st s)}).
    in_store_flag_unset_implies_desc_not_in_store st s /\ 
    points_to_nearest_desc_in_store st s Spec.MAdd

// only true when the add/evict set hashes have not diverged
let blum_store_inv (st:vstore) = 
  forall (s:slot_id{store_contains st s /\ MVal? (stored_value st s)}).
    evicted_to_blum_flag_unset_implies_desc_not_in_store st s /\ 
    points_to_nearest_desc_in_store st s Spec.BAdd

let store_contains_st_index (st:vstore) (s:slot_id{store_contains st s})
  : Lemma (s < Seq.length st)
          [SMTPat (store_contains st s)] 
  = admit()

let stored_value_matches_stored_key (st:vstore) (s:slot_id{store_contains st s}) 
  : Lemma (is_value_of (stored_key st s) (stored_value st s))
    [SMTPat (is_value_of (stored_key st s) (stored_value st s))]
  = admit()

let update_value_preserves_length 
      (st:vstore) 
      (s:slot_id{store_contains st s}) 
      (v:value_type_of (stored_key st s)) 
  : Lemma (let st' = update_value st s v in
           Seq.length st = Seq.length st')
          [SMTPat (update_value st s v)]  
  = admit()

let lemma_update_value_preserves_slots
      (st:vstore) 
      (s:slot_id{store_contains st s}) 
      (v:value_type_of (stored_key st s))
      (s':st_index st)
  : Lemma (store_contains st s' = store_contains (update_value st s v) s')
          [SMTPat (store_contains (update_value st s v) s')]
  = admit()

let lemma_update_value_preserves_keys 
  (st:vstore)
  (s:slot_id{store_contains st s}) 
  (v:value_type_of (stored_key st s))
  (s':slot_id{store_contains st s'})
  : Lemma (ensures stored_key st s' = stored_key (update_value st s v) s')
          [SMTPat (stored_key (update_value st s v) s')]
  = admit()

let lemma_update_in_store_preserves_slots
  (st:vstore)
  (s:slot_id{store_contains st s}) 
  (d:bin_tree_dir)
  (b:bool)
  (s':slot_id)
  : Lemma (ensures store_contains st s' = store_contains (update_in_store st s d b) s')
          [SMTPat (store_contains (update_in_store st s d b) s')]
  = admit()

let lemma_add_to_store_preserves_slots 
      (st:vstore) 
      (s:st_index st{not (store_contains st s)})
      (k:key) 
      (v:value_type_of k)
      (am:add_method)
      (s':slot_id{s <> s'})
  : Lemma (ensures store_contains st s' = store_contains (add_to_store st s k v am) s')
          [SMTPat (store_contains (add_to_store st s k v am) s')]
  = admit()

(* Relation between SC and S stores *)
let convert_entry (eo:option vstore_entry) : option SC.vstore_entry =
  match eo with
  | None -> None
  | Some e -> Some (SC.VStoreE e.k e.v e.am)
let equal_contents (st:vstore) (st':SC.vstore) : Type
  = Seq.equal (map convert_entry st) st'.SC.data

let lemma_equal_contents_store_contains
      (st:vstore)
      (st':SC.vstore)
      (s:slot_id)
  : Lemma (requires equal_contents st st')
          (ensures store_contains st s = SC.store_contains st' s)
          [SMTPat (store_contains st s); SMTPat (SC.store_contains st' s)]
  = admit()

let lemma_equal_contents_store_contains_key
      (st:vstore)
      (st':SC.vstore)
      (k:key)
  : Lemma (requires equal_contents st st')
          (ensures store_contains_key st k = SC.store_contains_key st' k)
          [SMTPat (store_contains_key st k); SMTPat (SC.store_contains_key st' k)]
  = admit()

let lemma_equal_contents_stored_key
      (st:vstore)
      (st':SC.vstore)
      (s:slot_id{store_contains st s})
  : Lemma (requires equal_contents st st')
          (ensures stored_key st s = SC.stored_key st' s)
          [SMTPat (stored_key st s); SMTPat (SC.stored_key st' s)]
  = admit()

let lemma_equal_contents_stored_value
      (st:vstore)
      (st':SC.vstore)
      (s:slot_id{store_contains st s})
  : Lemma (requires equal_contents st st')
          (ensures stored_value st s = SC.stored_value st' s)
          [SMTPat (stored_value st s); SMTPat (SC.stored_value st' s)]
  = admit()

let lemma_equal_contents_add_method_of
      (st:vstore)
      (st':SC.vstore)
      (s:slot_id{store_contains st s})
  : Lemma (requires equal_contents st st')
          (ensures add_method_of st s = SC.add_method_of st' s)
          [SMTPat (add_method_of st s); SMTPat (SC.add_method_of st' s)]
  = admit()

let lemma_equal_contents_update_value
  (st:vstore)
  (st':SC.vstore)
  (s:slot_id{store_contains st s}) 
  (v:value_type_of (stored_key st s))
  : Lemma (requires equal_contents st st')
          (ensures equal_contents (update_value st s v) (SC.update_store st' s v))
          [SMTPat (equal_contents (update_value st s v) (SC.update_store st' s v))]
  = admit()

let lemma_equal_contents_update_in_store
  (st:vstore)
  (st':SC.vstore)
  (s:slot_id{store_contains st s}) 
  (d:bin_tree_dir)
  (b:bool)
  : Lemma (requires equal_contents st st')
          (ensures equal_contents (update_in_store st s d b) st')
          [SMTPat (equal_contents (update_in_store st s d b) st')]
  = admit()

let lemma_equal_contents_add_to_store 
      (st:vstore) 
      (st':SC.vstore)
      (s:st_index st{not (store_contains st s)})
      (k:key) 
      (v:value_type_of k)
      (am:add_method)
  : Lemma (requires equal_contents st st')
          (ensures equal_contents (add_to_store st s k v am) (SC.add_to_store st' s k v am))
          [SMTPat (equal_contents (add_to_store st s k v am) (SC.add_to_store st' s k v am))]
  = admit()

let lemma_equal_contents_evict_from_store
      (st:vstore) 
      (st':SC.vstore)
      (s:st_index st{store_contains st s})
  : Lemma (requires equal_contents st st')
          (ensures equal_contents (evict_from_store st s) (SC.evict_from_store st' s))
          [SMTPat (equal_contents (evict_from_store st s) (SC.evict_from_store st' s))]
  = admit()
