module Zeta.Intermediate.Store

open Zeta.BinTree
open Zeta.App
open Zeta.Key
open Zeta.GenKey
open Zeta.Record
open Zeta.SeqAux
open Zeta.Intermediate.VerifierConfig
open Zeta.Intermediate.SlotKeyRel

module Spec = Zeta.High.Verifier
module GV = Zeta.GenericVerifier
module Merkle = Zeta.Merkle

(*** General Definitions & Basic Facts ***)

let add_method = Zeta.High.Verifier.add_method

(*
 * vstore_entry - reflect a Spec.vstore_entry with two additional fields tracking
 * whether a left/right descendant was added using merkle using this slot as "proof"
 *)
type vstore_entry (vcfg:verifier_config)  =
  | VStoreE: r:record vcfg.app ->
             am:add_method ->
             l_in_store : option (slot_id vcfg) ->
             r_in_store : option (slot_id vcfg) ->
             p: option (slot_id vcfg & bin_tree_dir) ->                     (* parent slot *)
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
  = not (inuse_slot st s)

let empty_slot_id #vcfg (st: vstore_raw vcfg) = s:slot_id vcfg{empty_slot st s}

(* key stored at an occupied slot *)
let stored_key #vcfg (st:vstore_raw vcfg) (s:inuse_slot_id st) : key vcfg.app
  = key_of (VStoreE?.r (Some?.v (get_slot st s)))

let stored_record #vcfg (st: vstore_raw vcfg) (s: inuse_slot_id st)
  : record vcfg.app
  = VStoreE?.r (Some?.v (get_slot st s))

let stored_base_key #vcfg (st: vstore_raw vcfg) (s:inuse_slot_id st) : base_key
  = to_base_key (stored_key st s)

(* is this a slot containing a merkle key *)
let merkle_slot_id #vcfg (st:vstore_raw vcfg)
  = s:inuse_slot_id st{IntK? (stored_key st s)}

let data_slot_id #vcfg (st:vstore_raw vcfg)
  = s:inuse_slot_id st{AppK? (stored_key st s)}

let stored_value #vcfg (st:vstore_raw vcfg) (s:inuse_slot_id st) : value vcfg.app
  = value_of (VStoreE?.r (Some?.v (get_slot st s)))

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

let parent_info #vcfg st s =
  VStoreE?.p (get_inuse_slot #vcfg st s)

(* does the slot s have a parent pointing to it *)
let has_parent #vcfg st s =
  Some? (parent_info #vcfg st s)

(* parent of slot s *)
let parent_slot #vcfg (st: vstore_raw vcfg) (s: inuse_slot_id st{has_parent st s}): slot_id vcfg =
  fst (Some?.v (parent_info #vcfg st s))

let parent_dir #vcfg (st: vstore_raw vcfg) (s: inuse_slot_id st{has_parent st s}): bin_tree_dir =
  snd (Some?.v (parent_info #vcfg st s))

(* if I have a parent, I should have been added with MAdd and the parent points to me *)
let parent_props_local #vcfg (st: vstore_raw vcfg) (s: slot_id vcfg) =
  inuse_slot st s ==>
  has_parent st s ==>
  (add_method_of st s = Spec.MAdd /\ points_to_dir st (parent_slot st s) (parent_dir st s) s)

(* parent implies madd holds for all slots in the store *)
let parent_props #vcfg (st: vstore_raw vcfg) =
  forall (s: slot_id vcfg). {:pattern parent_props_local st s} parent_props_local st s

(* a pointed slot is inuse *)
let points_to_inuse_local #vcfg (st:vstore_raw vcfg) (s1 s2: slot_id _) =
  (points_to_dir st s1 Left s2 ==> (inuse_slot st s2 /\ add_method_of st s2 = Spec.MAdd /\
                                  has_parent st s2 /\ parent_slot st s2 = s1 /\ parent_dir st s2 = Left)) /\
  (points_to_dir st s1 Right s2 ==> (inuse_slot st s2 /\ add_method_of st s2 = Spec.MAdd /\
                                    has_parent st s2 /\ parent_slot st s2 = s1 /\ parent_dir st s2 = Right))

let points_to_inuse #vcfg (st:vstore_raw vcfg) =
  forall (s1 s2: slot_id _). {:pattern (points_to_inuse_local st s1 s2) \/ (points_to st s1 s2)} points_to_inuse_local st s1 s2

let no_self_edge_local #vcfg (st: vstore_raw vcfg) (s: slot_id vcfg) =
  not (points_to st s s)

let no_self_edge #vcfg (st:vstore_raw vcfg) =
  forall s. {:pattern no_self_edge_local st s} no_self_edge_local st s

let madd_props_local #vcfg (st: vstore_raw vcfg) (s: slot_id vcfg) =
  inuse_slot st s ==>
  add_method_of st s = Spec.MAdd ==>
  stored_base_key st s <> Root ==>
  has_parent st s

let madd_props #vcfg (st: vstore_raw vcfg) =
  forall s. {:pattern madd_props_local st s} madd_props_local st s

(* vstore is a raw store that satisfies the points_to invariant *)
let vstore vcfg = st:vstore_raw vcfg{points_to_inuse st /\  parent_props st /\ madd_props st /\ no_self_edge st}

let empty_store vcfg:vstore vcfg = Seq.create (store_size vcfg) None

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
  (v:value vcfg.app {compatible (stored_key st s) v})
  : Tot (st':vstore vcfg {identical_except st st' s /\
                          inuse_slot st' s /\
                          (let VStoreE (k1,_) am1 ld1 rd1 p1 = get_inuse_slot st s in
                           let VStoreE (k2,v2) am2 ld2 rd2 p2 = get_inuse_slot st' s in
                           k1 = k2 /\ am1 = am2 /\ ld1 = ld2 /\ rd1 = rd2 /\ p1 = p2 /\ v2 = v)})

(*
 * add a new record to store with add method madd to slot s.
 * other paras: s' that points to none in direction d, but points to s
 * after the add
 *)
val madd_to_store
  (#vcfg: verifier_config)
  (st:vstore vcfg)
  (s:empty_slot_id st)
  (r:record vcfg.app)
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
                         parent_info st' s' = parent_info st s' /\

                         // slot s contains (k, v, MAdd) and points to nothing
                         inuse_slot st' s /\
                         get_inuse_slot st' s = VStoreE r Spec.MAdd None None (Some (s',d))
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
  (r: record vcfg.app)
  (s':merkle_slot_id st)
  (d:bin_tree_dir {points_to_some_slot st s' d})
  (d2:bin_tree_dir)
  : Tot (st': vstore vcfg{let od = other_dir d in
                          let s2 = pointed_slot st s' d in
                          let od2 = other_dir d2 in
                          let k,v = r in

                          // st and st' identical except at s, s'
                          identical_except3 st st' s s' s2 /\

                          // nothing changes in slot s', except it now points to s in direction d
                          inuse_slot st' s' /\
                          stored_key st' s' = stored_key st s' /\
                          stored_value st' s' = stored_value st s' /\
                          add_method_of st' s' = add_method_of st s' /\
                          points_to_dir st' s' d s /\
                          points_to_info st' s' od = points_to_info st s' od /\
                          parent_info st' s' = parent_info st s' /\

                          // slot s contains (k, v, MAdd) and points to s2 along direction d2
                          inuse_slot st' s /\
                          stored_key st' s = k /\ stored_value st' s = v /\ add_method_of st' s = Spec.MAdd /\
                          points_to_none st' s od2 /\
                          points_to_dir st' s d2 s2 /\
                          has_parent st' s /\
                          parent_slot st' s = s' /\
                          parent_dir st' s = d /\

                          has_parent st' s2 /\
                          parent_slot st' s2 = s /\
                          parent_dir st' s2 = d2 /\
                          inuse_slot st' s2 /\ inuse_slot st s2 /\
                          (let VStoreE r2' am2' ld2' rd2' _  = get_inuse_slot st' s2 in
                           let VStoreE r2 am2 ld2 rd2 _ = get_inuse_slot st s2 in
                           r2 = r2' /\ am2 = am2' /\ ld2 = ld2' /\ rd2 = rd2')})

val madd_to_store_root
  (#vcfg: verifier_config)
  (st:vstore vcfg)
  (s:empty_slot_id st)
  (v: value vcfg.app {IntV? v})
  : Tot (st':vstore vcfg{let r = IntK Root, v in
                         // st and st' identical except at s, s'
                         identical_except st st' s /\

                         // slot s contains (Root, v, MAdd) and points to none
                         inuse_slot st' s /\
                         get_inuse_slot st' s = VStoreE r Spec.MAdd None None None})

(* add a new entry (k,v) to the store at en empty slot s; *)
val badd_to_store
      (#vcfg:verifier_config)
      (st:vstore vcfg)
      (s:empty_slot_id st)
      (r: record vcfg.app)
  : Tot (st':vstore vcfg {// st and st' identical except for s
                          identical_except st st' s /\
                          inuse_slot st' s /\
                          get_inuse_slot st' s = VStoreE r Spec.BAdd None None None})

(*
 * evict the current entry from a store slot s; the entry should have been added using MAdd. From the
 * invariant of vstore, there is a unique slot s' that points to s. After the update s is empty
 * and the s' does not point to anything along the direction.
 *)
val mevict_from_store
  (#vcfg: verifier_config)
  (st:vstore vcfg)
  (s:inuse_slot_id st{points_to_none st s Left /\ points_to_none st s Right})
  (s':inuse_slot_id st{s <> s'})
  (d:bin_tree_dir{not (has_parent st s) /\ points_to_none st s' d \/
                  has_parent st s /\ parent_slot st s = s' /\ parent_dir st s = d})
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
                          points_to_none st' s' d /\
                          parent_info st' s' = parent_info st s'
                          })

(* evict the current entry from a store slot s that was added using BAdd *)
val bevict_from_store
  (#vcfg: verifier_config)
  (st:vstore vcfg)
  (s:inuse_slot_id st{points_to_none st s Left /\ points_to_none st s Right /\ add_method_of st s = Spec.BAdd})
  : Tot (st':vstore vcfg {// st and st' are identical except at slot s
                          identical_except st st' s /\

                          // slot s is empty after the update
                          empty_slot st' s})

(* any slot added with madd has another slot pointing to it; return one such pointing slot - which is unique in fact *)
val pointing_slot (#vcfg:_)
                (st:vstore vcfg)
                (s:inuse_slot_id st{IntK Root <> stored_key st s /\ add_method_of st s = Spec.MAdd})
 : Tot (s':inuse_slot_id st{points_to st s' s})


(*** Store Invariants ***)

(* In our correctness proof, we will want to maintain two invariants over stores:
   * is_map: there are no duplicate keys in the store, so there is a 1-to-1 mapping
     between the slot-based store and a standard key-value map
   * in_store_inv: the "desc_in_store" accurately reflect which the desc invariant
*)

(* No duplicate keys in the store *)
let is_map (#vcfg:verifier_config) (st:vstore vcfg) =
  forall (s1 s2:slot_id vcfg).
    (inuse_slot st s1 ==>
     inuse_slot st s2 ==>
     s1 <> s2 ==>
     stored_base_key st s1 <> stored_base_key st s2)

let elim_is_map (#vcfg:_) (st:vstore vcfg)
                (s:inuse_slot_id st)
                (s':inuse_slot_id st{s' <> s})
  : Lemma (requires is_map st)
          (ensures stored_base_key st s ≠ stored_base_key st s')
  = ()

(* a store that is a map *)
let ismap_vstore vcfg = st:vstore vcfg{is_map st}

(* does the store contain a specified key *)
val store_contains_key (#vcfg:_) (st:ismap_vstore vcfg) (k:base_key):
  b:bool{b <==> (exists (s: slot_id vcfg). inuse_slot st s /\ stored_base_key st s = k)}

val slot_of_key
  (#vcfg:_)
  (st:ismap_vstore vcfg)
  (k: base_key{store_contains_key st k})
  : Tot (s: inuse_slot_id st {k = stored_base_key st s})

(* updating a value preserves is_map *)
val lemma_ismap_update_value (#vcfg:_)
  (st:ismap_vstore vcfg)
  (s:inuse_slot_id st)
  (v:value vcfg.app {compatible (stored_key st s) v})
  : Lemma (ensures (is_map (update_value st s v)))
          [SMTPat (update_value st s v)]

val lemma_ismap_madd_to_store (#vcfg:_) (st:ismap_vstore vcfg)
  (s:empty_slot_id st)
  (r: record vcfg.app)
  (s':merkle_slot_id st)
  (d:bin_tree_dir {points_to_none st s' d})
  : Lemma (requires (let bk = to_base_key (key_of r) in
                     not (store_contains_key st bk)))
          (ensures (is_map (madd_to_store st s r s' d)))
          [SMTPat (madd_to_store st s r s' d)]

val lemma_ismap_madd_to_store_split
  (#vcfg: verifier_config)
  (st:ismap_vstore vcfg)
  (s:empty_slot_id st)
  (r: record vcfg.app)
  (s':merkle_slot_id st)
  (d:bin_tree_dir {points_to_some_slot st s' d})
  (d2:bin_tree_dir)
  : Lemma (requires (let bk = to_base_key (key_of r) in
                     not (store_contains_key st bk)))
          (ensures (is_map (madd_to_store_split st s r s' d d2)))
          [SMTPat (madd_to_store_split st s r s' d d2)]

(* if two slots of an ismap store contain the same key, then the two slots should be identical *)
val lemma_ismap_correct (#vcfg:_) (st:ismap_vstore vcfg) (s1 s2: inuse_slot_id st)
  : Lemma (requires (stored_base_key st s1 = stored_base_key st s2))
          (ensures (s1 = s2))

val lemma_empty_store_is_map (#vcfg:_):
  Lemma (ensures (is_map (empty_store vcfg)))
        [SMTPat (empty_store vcfg)]

(* an empty store contains no key *)
val lemma_empty_contains_nokey (#vcfg:_) (k:base_key):
  Lemma (ensures (let st = empty_store vcfg in
                  not (store_contains_key st k)))

(* is_map is preserved when adding a new key *)
val lemma_madd_root_to_store_is_map
      (#vcfg:_)
      (st:ismap_vstore vcfg{not (store_contains_key st Root)})
      (s:empty_slot_id st)
      (v:value vcfg.app {IntV? v})
  : Lemma (ensures (is_map (madd_to_store_root st s v)))

(*** Relation w/ Spec-level Stores ***)


let store_rel_key (#vcfg:_) (st: ismap_vstore vcfg) (stk: Spec.store_t vcfg.app) (k: base_key)
  = (store_contains_key st k = Spec.store_contains stk k) /\
         (store_contains_key st k ==>
         (let s = slot_of_key st k in
          stored_key st s = Spec.stored_key stk k /\
          stored_value st s = Spec.stored_value stk k /\
          add_method_of st s = Spec.add_method_of stk k))

(* Relation between stores *)
let store_rel (#vcfg:_) (st:vstore vcfg) (st':Spec.store_t vcfg.app)  =
  is_map st /\
  (forall (k:base_key). (store_contains_key st k = Spec.store_contains st' k) /\
         (store_contains_key st k ==>
         (let s = slot_of_key st k in
          stored_key st s = Spec.stored_key st' k /\
          stored_value st s = Spec.stored_value st' k /\
          add_method_of st s = Spec.add_method_of st' k)))

let elim_key_store_rel (#vcfg:_) (sts: vstore vcfg) (stk: Spec.store_t vcfg.app) (k: base_key)
  : Lemma (requires (store_rel sts stk))
          (ensures (store_rel_key sts stk k))
  = ()

(** Any store can be viewed as an instance of slot-key map *)
let to_slot_state_map #vcfg (st:vstore_raw vcfg): slot_state_map _ =
  fun s -> if inuse_slot st s then Assoc (stored_base_key st s) else Free

(* the property that slot pointing to implies merkle value pointing to *)
let slot_points_to_is_merkle_points_to_local
  (#vcfg:_)
  (st: vstore vcfg)
  (s1 s2: slot_id vcfg)
  (d: bin_tree_dir) =
    points_to_dir st s1 d s2 ==>
    (let k1 = stored_base_key st s1 in
     let k2 = stored_base_key st s2 in
     is_merkle_key k1 /\
     (let v1 = to_merkle_value (stored_value st s1) in
      Merkle.points_to v1 d k2))

let slot_points_to_is_merkle_points_to (#vcfg:_) (st: vstore vcfg) =
  forall (s1 s2: slot_id _) (d:_). slot_points_to_is_merkle_points_to_local st s1 s2 d

let mv_points_to_in_some_dir (v: Merkle.value) (k:base_key): bool =
  Merkle.points_to v Left k ||
  Merkle.points_to v Right k

let merkle_points_to_uniq_local (#vcfg: _) (st: vstore vcfg) (s1 s2: slot_id vcfg) (k: base_key): bool =
  s1 = s2 ||
  empty_slot st s1 || not (is_merkle_key (stored_base_key st s1)) ||
  empty_slot st s2 || not (is_merkle_key (stored_base_key st s2)) ||
  (let mv1 = to_merkle_value (stored_value st s1) in
   let mv2 = to_merkle_value (stored_value st s2) in
   not (mv_points_to_in_some_dir mv1 k && mv_points_to_in_some_dir mv2 k))

let merkle_points_to_uniq (#vcfg: _) (st: vstore vcfg) =
  forall s1 s2 k. {:pattern merkle_points_to_uniq_local st s1 s2 k} merkle_points_to_uniq_local st s1 s2 k

let merkle_points_to_desc_local (#vcfg:_) (st: vstore vcfg) (s: slot_id vcfg) (d: bin_tree_dir): bool =
  empty_slot st s || not (is_merkle_key (stored_base_key st s)) ||
  (let mv = to_merkle_value (stored_value st s) in
   Merkle.points_to_none mv d ||
   (is_proper_desc (Merkle.pointed_key mv d) (stored_base_key st s) &&
    d = desc_dir (Merkle.pointed_key mv d) (stored_base_key st s)))

let merkle_points_to_desc (#vcfg:_) (st: vstore vcfg) =
  forall s d. {:pattern merkle_points_to_desc_local st s d} merkle_points_to_desc_local st s d

val lemma_not_contains_after_mevict
  (#vcfg: verifier_config)
  (st:ismap_vstore vcfg)
  (s:inuse_slot_id st{points_to_none st s Left /\ points_to_none st s Right})
  (s':inuse_slot_id st{s <> s'})
  (d:bin_tree_dir{not (has_parent st s) /\ points_to_none st s' d \/
                  has_parent st s /\ parent_slot st s = s' /\ parent_dir st s = d}):
  Lemma (ensures (let st' = mevict_from_store st s s' d in
                  let k = stored_base_key st s in
                  is_map st' /\
                  not (store_contains_key st' k)))
        [SMTPat (mevict_from_store st s s' d)]

val lemma_not_contains_after_bevict
  (#vcfg: verifier_config)
  (st:ismap_vstore vcfg)
  (s:inuse_slot_id st{points_to_none st s Left /\ points_to_none st s Right /\ add_method_of st s = Spec.BAdd})
  : Lemma (ensures (let st' = bevict_from_store st s in
                    let k = stored_base_key st s in
                    is_map st' /\
                    not (store_contains_key st' k)))
          [SMTPat (bevict_from_store st s)]

val lemma_ismap_badd_to_store (#vcfg:_) (st:ismap_vstore vcfg)
  (s:empty_slot_id st)
  (r: record vcfg.app)
  : Lemma (requires (let bk = to_base_key (key_of r) in
                     not (store_contains_key st bk)))
          (ensures (is_map (badd_to_store st s r)))
          [SMTPat (badd_to_store st s r)]

val store_rel_slot (#vcfg:_) (st: ismap_vstore vcfg) (st':_ {store_rel st st'}) (s: inuse_slot_id st)
  : Lemma (ensures (let k = stored_base_key st s in
                    Spec.store_contains st' k /\
                    stored_key st s = Spec.stored_key st' k /\
                    stored_value st s = Spec.stored_value st' k /\
                    add_method_of st s = Spec.add_method_of st' k))

module S = FStar.Seq

(* does a slot contain an app key *)
let contains_app_key (#vcfg:_) (st: vstore vcfg) (s: slot_id vcfg)
  = inuse_slot st s &&
    AppK? (stored_key st s)

(* a sequence of base keys contain only appln keys *)
let contains_only_app_keys (#vcfg:_) (st: vstore vcfg) (ss: S.seq (slot_id vcfg))
  = forall i. contains_app_key st (S.index ss i)

let contains_only_app_keys_comp (#vcfg:_) (st: vstore vcfg) (ss: S.seq (slot_id vcfg))
  : b:bool {b <==> contains_only_app_keys st ss}
  = let open Zeta.SeqIdx in
    not (exists_elems_with_prop_comp (fun s -> not (contains_app_key st s)) ss)

val puts_store (#vcfg:_)
  (st: vstore vcfg)
  (ss: S.seq (slot_id vcfg) {contains_only_app_keys st ss})
  (ws: S.seq (app_value_nullable vcfg.app.adm){S.length ws = S.length ss})
  : vstore vcfg

(* preserves everything but the value *)
val puts_preserves (#vcfg:_)
  (st: vstore vcfg)
  (ss: S.seq (slot_id vcfg){contains_only_app_keys st ss})
  (ws: S.seq (app_value_nullable vcfg.app.adm){S.length ws = S.length ss})
  (s: slot_id vcfg)
  : Lemma (ensures (let st_ = puts_store st ss ws in
                    inuse_slot st s = inuse_slot st_ s /\
                    (inuse_slot st s ==> (
                      stored_key st s = stored_key st_ s /\
                      add_method_of st s = add_method_of st_ s /\
                      points_to_info st s Left = points_to_info st_ s Left /\
                      points_to_info st s Right = points_to_info st_ s Right /\
                      parent_info st s = parent_info st_ s))))

(* for non-referenced slots, it preserves everything ... *)
val puts_preserves_non_ref (#vcfg:_)
  (st: vstore vcfg)
  (ss: S.seq (slot_id vcfg){contains_only_app_keys st ss})
  (ws: S.seq (app_value_nullable vcfg.app.adm){S.length ws = S.length ss})
  (s: slot_id vcfg)
  : Lemma (ensures (let st_ = puts_store st ss ws in
                    not (S.mem s ss) ==>
                    get_slot st s = get_slot st_ s))

val puts_preserve_ismap (#vcfg:_)
  (st: ismap_vstore vcfg)
  (ss: S.seq (slot_id vcfg){contains_only_app_keys st ss})
  (ws: S.seq (app_value_nullable vcfg.app.adm){S.length ws = S.length ss})
  : Lemma (ensures (is_map (puts_store st ss ws)))
          [SMTPat (puts_store st ss ws)]

val puts_ref_value (#vcfg:_)
  (st: vstore vcfg)
  (ss: S.seq (slot_id vcfg){contains_only_app_keys st ss})
  (ws: S.seq (app_value_nullable vcfg.app.adm){S.length ws = S.length ss})
  (s: slot_id vcfg {S.mem s ss})
  : Lemma (ensures (let i = S.index_mem s ss in
                    let sts_ = puts_store st ss ws in
                    inuse_slot sts_ s /\
                    stored_value sts_ s = AppV (S.index ws i)))
