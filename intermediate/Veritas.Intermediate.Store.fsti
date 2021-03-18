module Veritas.Intermediate.Store

open Veritas.BinTree
open Veritas.Key
open Veritas.Record
open Veritas.SeqAux
open Veritas.Intermediate.VerifierConfig
open Veritas.Intermediate.SlotKeyRel

module Spec = Veritas.Verifier
module FE = FStar.FunctionalExtensionality

(*** General Definitions & Basic Facts ***)

let add_method = Veritas.Verifier.add_method

(* 
 * vstore_entry - reflect a Spec.vstore_entry with two additional fields tracking 
 * whether a left/right descendant was added using merkle using this slot as "proof"
 *)
type vstore_entry (vcfg:verifier_config) = 
  | VStoreE: k:key -> 
             v:value_type_of k -> 
             am:add_method -> 
             l_in_store : option (slot_id vcfg) -> 
             r_in_store : option (slot_id vcfg) -> 
             vstore_entry vcfg

(* vstore_raw: the raw version of the vstore; the actual vstore 
 * is the raw version with some invariants *)
let vstore_raw vcfg = st:Seq.seq (option (vstore_entry vcfg)){Seq.length st = store_size vcfg}

let get_slot #vcfg (st:vstore_raw vcfg) (s: slot_id vcfg)
  : option (vstore_entry vcfg)
  = Seq.index st s

(* return true if s is a valid slot that is occupied *)
let inuse_slot #vcfg (st:vstore_raw vcfg) (s:slot_id vcfg) : bool
  = Some? (get_slot st s)

(* dep type of all slots in use *)
let inuse_slot_id #vcfg (st: vstore_raw vcfg) = s:slot_id vcfg{inuse_slot st s}

let get_inuse_slot #vcfg (st:vstore_raw vcfg) (s:inuse_slot_id st) =
  Some?.v (get_slot st s)

(* is this an empty slot *)
let empty_slot #vcfg (st:vstore_raw vcfg) (s:slot_id vcfg): bool 
  = None = get_slot st s

let empty_slot_id #vcfg (st: vstore_raw vcfg) = s:slot_id vcfg{empty_slot st s}

(* key stored at an occupied slot *)
let stored_key #vcfg (st:vstore_raw vcfg) (s:inuse_slot_id st) : key
  = VStoreE?.k (Some?.v (get_slot st s))

(* is this a slot containing a merkle key *)
let merkle_slot_id #vcfg (st:vstore_raw vcfg)
  = s:inuse_slot_id st{is_merkle_key (stored_key st s)}

let data_slot_id #vcfg (st:vstore_raw vcfg)
  = s:inuse_slot_id st{is_data_key (stored_key st s)}

let stored_value #vcfg (st:vstore_raw vcfg) (s:inuse_slot_id st) : value_type_of (stored_key st s)
  = VStoreE?.v (Some?.v (get_slot st s))

let add_method_of #vcfg (st:vstore_raw vcfg) (s:inuse_slot_id st) : add_method
  = VStoreE?.am (Some?.v (get_slot st s))

let points_to_info #vcfg (st:vstore_raw vcfg) (s:inuse_slot_id st) (d:bin_tree_dir) = 
  match d with
  | Left -> VStoreE?.l_in_store (Some?.v (get_slot st s))
  | Right -> VStoreE?.r_in_store (Some?.v (get_slot st s))

(* does the slot point to some slot along a direction *)
let points_to_some_slot #vcfg (st:vstore_raw vcfg) (s: inuse_slot_id st) (d:bin_tree_dir): bool =
  Some? (points_to_info st s d)
  
let points_to_none #vcfg (st: vstore_raw vcfg) (s: inuse_slot_id st) (d: bin_tree_dir): bool =
  None? (points_to_info st s d)
   
let pointed_slot #vcfg (st:vstore_raw vcfg) (s:inuse_slot_id st) (d:bin_tree_dir{points_to_some_slot st s d}): slot_id vcfg
  = Some?.v (points_to_info st s d)

let points_to_dir #vcfg (st:vstore_raw vcfg) (s1: slot_id vcfg) (d:bin_tree_dir) (s2: slot_id vcfg) = 
  inuse_slot st s1 &&
  points_to_some_slot st s1 d && pointed_slot st s1 d = s2

(* points to relation of slots *)
let points_to #vcfg (st:vstore_raw vcfg) (s1:slot_id vcfg) (s2:slot_id vcfg) = 
  points_to_dir st s1 Left s2 ||
  points_to_dir st s1 Right s2

(* the point of this trivial lemma is to trigger the SMTPat below; TODO: is their an idiomatically better way? *)
let lemma_points_to_dir_implies_points_to #vcfg (st:vstore_raw vcfg) (s1: slot_id vcfg) (d:bin_tree_dir) (s2: slot_id vcfg):
  Lemma (requires (points_to_dir st s1 d s2))
        (ensures (points_to st s1 s2))
        [SMTPat (points_to_dir st s1 d s2)] = ()

(* a pointed slot is inuse *)
let points_to_inuse_local #vcfg (st:vstore_raw vcfg) (s1 s2: slot_id _) = 
  points_to st s1 s2 ==> inuse_slot st s2

let points_to_inuse #vcfg (st:vstore_raw vcfg) = 
  forall (s1 s2: slot_id _). {:pattern (points_to_inuse_local st s1 s2) \/ (points_to st s1 s2)} points_to_inuse_local st s1 s2

(* a node is pointed to by at most one node *)
let points_to_uniq_local #vcfg (st:vstore_raw vcfg) (s1 s2 s: slot_id vcfg) = 
  s1 = s2 || not (points_to st s1 s) || not (points_to st s2 s)

let points_to_uniq #vcfg (st:vstore_raw vcfg) = 
  forall (s1 s2 s: slot_id vcfg). {:pattern points_to_uniq_local st s1 s2 s} points_to_uniq_local st s1 s2 s

let pointed_to_inv_local #vcfg (st:vstore_raw vcfg) (s:slot_id vcfg) = 
  inuse_slot st s ==> 
  stored_key st s <> Root ==>
  add_method_of st s = Spec.MAdd ==> 
  (exists (s': inuse_slot_id st). exists (d:bin_tree_dir).   
     points_to_some_slot st s' d /\
     pointed_slot st s' d = s)

let pointed_to_inv #vcfg (st:vstore_raw vcfg) = 
  forall (s: slot_id vcfg). {:pattern pointed_to_inv_local st s} pointed_to_inv_local st s

(* vstore is a raw store that satisfies the points_to invariant *)
let vstore vcfg = st:vstore_raw vcfg{points_to_inuse st /\  points_to_uniq st /\ pointed_to_inv st}

let empty_store vcfg:vstore vcfg = Seq.create (store_size vcfg) None
  
let has_key #vcfg (k:key) (e:option (vstore_entry vcfg)) : bool
  = match e with
    | Some (VStoreE k' _ _ _ _) -> k = k'
    | None -> false

(** vstore update methods **)

(* two stores st1 and st2 are identical everywhere except in slot s *)
let identical_except #vcfg (st1 st2: vstore_raw vcfg) (s: slot_id vcfg) =
  forall (s': slot_id vcfg). s' <> s ==> get_slot st1 s' = get_slot st2 s'

let identical_except2 #vcfg (st1 st2: vstore_raw vcfg) (s1 s2: slot_id vcfg) = 
  forall (s': slot_id vcfg). s' <> s1 ==> s' <> s2 ==> get_slot st1 s' = get_slot st2 s'

let identical_except3 #vcfg (st1 st2: vstore_raw vcfg) (s1 s2 s3: slot_id vcfg) = 
  forall (s': slot_id vcfg). s' <> s1 ==> s' <> s2 ==> s' <> s3 ==> get_slot st1 s' = get_slot st2 s'

(* update a value of a key *)
val update_value 
  (#vcfg:_)
  (st:vstore vcfg)
  (s:inuse_slot_id st)
  (v:value_type_of (stored_key st s))
  : Tot (st':vstore vcfg {identical_except st st' s /\
                          inuse_slot st' s /\
                          v = stored_value st' s /\
                          (let VStoreE k1 _ am1 ld1 rd1 = get_inuse_slot st s in
                           let VStoreE k2 _ am2 ld2 rd2 = get_inuse_slot st' s in
                           k1 = k2 /\ am1 = am2 /\ ld1 = ld2 /\ rd1 = rd2)})

(* 
 * add a new record to store with add method madd to slot s.
 * other paras: s' that points to none in direction d, but points to s 
 * after the add
 *)
val madd_to_store
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

(* 
 * add a new record to store with add method madd to slot s.
 * other paras: s' that points s2 in direction d; after the add
 * s' -> s (along d) and s -> s2 (along d2, a parameter)
 *)
val madd_to_store_split 
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

val madd_to_store_root
  (#vcfg: verifier_config)
  (st:vstore vcfg)
  (s:empty_slot_id st)
  (v:value_type_of Root)
  : Tot (st':vstore vcfg{// st and st' identical except at s, s'
                         identical_except st st' s /\

                         // slot s contains (Root, v, MAdd) and points to none 
                         inuse_slot st' s /\
                         get_inuse_slot st' s = VStoreE Root v Spec.MAdd None None})                        

(* add a new entry (k,v) to the store at en empty slot s; *)
val badd_to_store 
      (#vcfg:verifier_config)
      (st:vstore vcfg) 
      (s:empty_slot_id st)
      (k:key) 
      (v:value_type_of k) 
  : Tot (st':vstore vcfg {// st and st' identical except for s
                          identical_except st st' s /\
                          inuse_slot st' s /\
                          get_inuse_slot st' s = VStoreE k v Spec.BAdd None None})

(* 
 * evict the current entry from a store slot s; the entry should have been added using MAdd. From the 
 * invariant of vstore, there is a unique slot s' that points to s. After the update s is empty 
 * and the s' does not point to anything along the direction.
 *)
val mevict_from_store 
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
                          stored_key st' s' = stored_key st s' /\
                          stored_value st' s' = stored_value st s' /\
                          add_method_of st' s' = add_method_of st s' /\
                          points_to_info st' s' od = points_to_info st s' od /\
                          points_to_none st' s' d
                          })

(* evict the current entry from a store slot s that was added using BAdd *)
val bevict_from_store
  (#vcfg: verifier_config)
  (st:vstore vcfg)
  (s:inuse_slot_id st{points_to_none st s Left /\ points_to_none st s Right})
  : Tot (st':vstore vcfg {// st and st' are identical except at slot s 
                          identical_except st st' s /\

                          // slot s is empty after the update
                          empty_slot st' s})

(* any slot added with madd has another slot pointing to it; return one such pointing slot - which is unique in fact *)
val pointing_slot (#vcfg:_) 
                (st:vstore vcfg) 
                (s:inuse_slot_id st{Root <> stored_key st s /\ add_method_of st s = Spec.MAdd})
 : Tot (s':inuse_slot_id st{points_to st s' s})


(*** Store Invariants ***)

(* In our correctness proof, we will want to maintain two invariants over stores:
   * is_map: there are no duplicate keys in the store, so there is a 1-to-1 mapping
     between the slot-based store and a standard key-value map
   * in_store_inv: the "desc_in_store" accurately reflect which the desc invariant
*)

(* No duplicate keys in the store *)
let is_map (#vcfg:_) (st:vstore vcfg) =
  forall (s:inuse_slot_id st) 
    (s':inuse_slot_id st{s' <> s}). 
        // TODO: this pattern is pretty general -- it may lead to proof performance issues
        {:pattern (Seq.index st s); (Seq.index st s')} 
    stored_key st s <> stored_key st s'

let elim_is_map (#vcfg:_) (st:vstore vcfg) 
                (s:inuse_slot_id st)
                (s':inuse_slot_id st{s' <> s})
  : Lemma (requires is_map st)
          (ensures stored_key st s ≠ stored_key st s')
  = ()

(* a store that is a map *)
let ismap_vstore vcfg = st:vstore vcfg{is_map st}

(* convert a slot-indexed store to a key-indexed store *)
val as_map (#vcfg:_) (st:ismap_vstore vcfg) : Spec.vstore

let store_contains_key #vcfg (st:ismap_vstore vcfg) (k:key) = 
  Spec.store_contains (as_map st) k

(* updating a value preserves is_map *)
val lemma_ismap_update_value (#vcfg:_) (st:ismap_vstore vcfg) (s:inuse_slot_id st) (v:value_type_of (stored_key st s))
  : Lemma (ensures (is_map (update_value st s v)))
          [SMTPat (update_value st s v)]

val lemma_ismap_madd_to_store (#vcfg:_) (st:ismap_vstore vcfg)
  (s:empty_slot_id st)
  (k:key) (v:value_type_of k)
  (s':merkle_slot_id st)
  (d:bin_tree_dir {points_to_none st s' d})
  : Lemma (requires (not (store_contains_key st k)))
          (ensures (is_map (madd_to_store st s k v s' d)))
          [SMTPat (madd_to_store st s k v s' d)]

val lemma_ismap_madd_to_store_split 
  (#vcfg: verifier_config)
  (st:ismap_vstore vcfg)
  (s:empty_slot_id st)
  (k:key) (v:value_type_of k)
  (s':merkle_slot_id st)
  (d:bin_tree_dir {points_to_some_slot st s' d})
  (d2:bin_tree_dir)  
  : Lemma (requires (not (store_contains_key st k)))
          (ensures (is_map (madd_to_store_split st s k v s' d d2)))
          [SMTPat (madd_to_store_split st s k v s' d d2)]

(* if two slots of an ismap store contain the same key, then the two slots should be identical *)
val lemma_ismap_correct (#vcfg:_) (st:ismap_vstore vcfg) (s1 s2: inuse_slot_id st)
  : Lemma (requires (stored_key st s1 = stored_key st s2))
          (ensures (s1 = s2))
          
val lemma_empty_store_is_map (#vcfg:_):
  Lemma (ensures (is_map (empty_store vcfg)))
        [SMTPat (empty_store vcfg)]
        
(* an empty store contains no key *)
val lemma_empty_contains_nokey (#vcfg:_) (k:key):
  Lemma (ensures (let st = empty_store vcfg in
                  not (store_contains_key st k)))

(* is_map is preserved when adding a new key *)
val lemma_madd_root_to_store_is_map
      (#vcfg:_)
      (st:ismap_vstore vcfg{not (store_contains_key st Root)}) 
      (s:empty_slot_id st) 
      (v:value_type_of Root) 
  : Lemma (ensures (is_map (madd_to_store_root st s v)))

(*** Relation w/ Spec-level Stores ***)

val lemma_as_map_empty (vcfg:_)
  : Lemma (ensures (let st = empty_store vcfg in
                     forall (k:key). as_map st k = None))

val lemma_as_map_slot_key_equiv (#vcfg:_) (st:ismap_vstore vcfg) (s:inuse_slot_id _)
  : Lemma (ensures (let k = stored_key st s in
                    let stk = as_map st in
                    Spec.store_contains stk k /\
                    stored_value st s = Spec.stored_value stk k /\
                    add_method_of st s = Spec.add_method_of stk k))
          [SMTPat (inuse_slot st s)]

val slot_of_key (#vcfg:_) (st:ismap_vstore vcfg) (k: key{let stk = as_map st in
                                                         Spec.store_contains stk k})
  : Tot (s: inuse_slot_id st {let stk = as_map st in
                              k = stored_key st s /\
                              stored_value st s = Spec.stored_value stk k /\
                              add_method_of st s = Spec.add_method_of stk k})

(* Relation between stores *)
let store_rel (#vcfg:_) (st:vstore vcfg) (st':Spec.vstore) : Type = 
  is_map st /\ FE.feq st' (as_map st)

(** Any store can be viewed as an instance of slot-key map *)
let to_slot_state_map #vcfg (st:vstore_raw vcfg): slot_state_map _ = 
  fun s -> if inuse_slot st s then Assoc (stored_key st s) else Free

(* the property that slot pointing to implies merkle value pointing to *)
let slot_points_to_is_merkle_points_to_local
  (#vcfg:_) 
  (st: vstore vcfg)
  (s1 s2: slot_id vcfg)
  (d: bin_tree_dir) =  
    points_to_dir st s1 d s2 ==> 
    (let k1 = stored_key st s1 in
     let k2 = stored_key st s2 in
     is_merkle_key k1 /\
     (let v1 = to_merkle_value (stored_value st s1) in
      mv_points_to v1 d k2))

let slot_points_to_is_merkle_points_to (#vcfg:_) (st: vstore vcfg) = 
  forall (s1 s2: slot_id _). forall d. slot_points_to_is_merkle_points_to_local st s1 s2 d

