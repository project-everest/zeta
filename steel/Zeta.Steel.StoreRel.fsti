module Zeta.Steel.StoreRel

(* This module sets up the relationship between steel store and spec-level store *)

open Zeta.App
open Zeta.Steel.KeyUtils
open Zeta.Steel.Rel

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module L = FStar.List.Tot
module GK = Zeta.GenKey
module K = Zeta.Key
module M = Zeta.Merkle
module GV = Zeta.GenericVerifier
module IL = Zeta.Intermediate.Logs
module IV = Zeta.Intermediate.Verifier
module AT = Zeta.Steel.ApplicationTypes
module T = Zeta.Steel.FormatsManual
module TSM = Zeta.Steel.ThreadStateModel

let related_in_store_tag (st: option s_slot_id_r) (it: option i_slot_id)
  = match st, it with
    | None, None -> True
    | Some ss, Some is -> related_slot_r ss is /\ True
    | _ -> False

let related_parent_slot (s: option (s_slot_id_r & s_dir)) (i: option (i_slot_id & i_dir))
  = match s, i with
    | None, None -> True
    | Some (ss, sd), Some (is, id) ->
      related_slot ss is /\
      related_desc_dir sd id
    | _ -> False

let related_store_entry (s: s_store_entry) (i: i_store_entry)
  = let Zeta.Intermediate.Store.VStoreE r am ld rd p = i in
    related_record (s.key, s.value) r /\
    related_add_method s.add_method am /\
    related_in_store_tag s.l_child_in_store ld /\
    related_in_store_tag s.r_child_in_store rd /\
    related_parent_slot s.parent_slot p

let related_store_entry_opt (s: option s_store_entry) (i: option i_store_entry)
  = match s, i with
    | None, None -> True
    | Some s, Some i -> related_store_entry s i
    | _ -> False

let related_store (ss: s_store) (is: i_store)
  = forall i. related_store_entry_opt (Seq.index ss i) (Seq.index is i)

#push-options "--fuel 0 --ifuel 0 --query_stats"

let get_slot (st: s_store) (s: T.slot)
  = Seq.index st (U16.v s)

#pop-options

let inuse_slot (st: s_store) (s: T.slot)
  = Some? (get_slot st s)

let empty_slot (st: s_store) (s: T.slot)
  = not (inuse_slot st s)

let stored_key (st: s_store) (s: T.slot{inuse_slot st s})
  = let Some e = get_slot st s in
    e.key

let stored_base_key (st: s_store) (s: T.slot{inuse_slot st s})
  = TSM.to_base_key (stored_key st s)

let stored_value (st: s_store) (s: T.slot{inuse_slot st s})
  = let Some e = get_slot st s in
    e.value

let add_method_of (st: s_store) (s: T.slot{inuse_slot st s})
  = let Some e = get_slot st s in
    e.add_method

let points_to_info (st: s_store) (s: T.slot{inuse_slot st s}) (d: bool)
  = let Some e = get_slot st s in
    if d then e.l_child_in_store
    else e.r_child_in_store

let points_to_some_slot (st: s_store) (s: T.slot{inuse_slot st s}) (d: bool)
  = Some? (points_to_info st s d)

let points_to_none (st: s_store) (s: T.slot{inuse_slot st s}) (d: bool)
  = not (points_to_some_slot st s d)

let pointed_slot (st: s_store) (s: T.slot{inuse_slot st s}) (d: bool{points_to_some_slot st s d})
  = let Some s = points_to_info st s d in
    s

let points_to_dir (st: s_store) (s1: T.slot) (d: bool) (s2: T.slot)
  = inuse_slot st s1 &&
    points_to_some_slot st s1 d &&
    pointed_slot st s1 d = s2

let points_to (st: s_store) (s1 s2:_)
  = points_to_dir st s1 true s2 ||
    points_to_dir st s1 false s2

let has_parent (st: s_store) (s: T.slot {inuse_slot st s})
  = let Some e = get_slot st s in
    Some? e.parent_slot

let parent_slot (st: s_store) (s: T.slot {inuse_slot st s /\ has_parent st s})
  : T.slot
  = let Some e = get_slot st s in
    let Some (ps,_) = e.parent_slot in
    ps

let parent_dir (st: s_store) (s: T.slot {inuse_slot st s /\ has_parent st s})
  : bool
  = let Some e = get_slot st s in
    let Some (_,d) = e.parent_slot in
    d

let parent_info (st: s_store) (s: T.slot {inuse_slot st s})
  = let Some e = get_slot st s in
    e.parent_slot

(* if I have a parent, I should have been added with MAdd and the parent points to me *)
let parent_props_local (st: s_store) (s: T.slot) =
  inuse_slot st s ==>
  has_parent st s ==>
  (add_method_of st s = TSM.MAdd /\ points_to_dir st (parent_slot st s) (parent_dir st s) s)

let parent_props (st: s_store)
  = forall s. parent_props_local st s

let points_to_inuse_local (st: s_store) (s1 s2: T.slot)
  = (points_to_dir st s1 true s2 ==> (inuse_slot st s2 /\ add_method_of st s2 = TSM.MAdd /\
                                      has_parent st s2 /\ parent_slot st s2 = s1 /\ parent_dir st s2 = true)) /\
    (points_to_dir st s1 false s2 ==> (inuse_slot st s2 /\ add_method_of st s2 = TSM.MAdd /\
                                      has_parent st s2 /\ parent_slot st s2 = s1 /\ parent_dir st s2 = false))

let points_to_inuse (st: s_store)
  = forall (s1 s2:T.slot). points_to_inuse_local st s1 s2

let no_self_edges_local (st: s_store) (s: T.slot)
  = not (points_to st s s)

let no_self_edges (st: s_store)
  = forall s. no_self_edges_local st s

let all_props (st: s_store)
  = parent_props st /\
    points_to_inuse st /\
    no_self_edges st

val lemma_related_implies_all_props (st: s_store) (i_st: i_store)
  : Lemma (requires (related_store st i_st))
          (ensures (all_props st))

(* two stores st1 and st2 are identical everywhere except in slot s *)
let identical_except (st1 st2: s_store) (s: T.slot) =
  forall (s': T.slot). s' <> s ==> get_slot st1 s' == get_slot st2 s'

let identical_except2 (st1 st2: s_store) (s1 s2: T.slot) =
  forall (s': T.slot). s' <> s1 ==> s' <> s2 ==> get_slot st1 s' == get_slot st2 s'

let identical_except3 (st1 st2: s_store) (s1 s2 s3: T.slot) =
  forall (s': T.slot). s' <> s1 ==> s' <> s2 ==> s' <> s3 ==> get_slot st1 s' == get_slot st2 s'

(* two thread states are identical except for their stores *)
let identical_except_store (tsm1 tsm2: TSM.thread_state_model)
  = tsm1.failed == tsm2.failed /\
    tsm1.clock == tsm2.clock /\
    tsm1.epoch_hashes == tsm2.epoch_hashes /\
    tsm1.thread_id == tsm2.thread_id /\
    tsm1.app_results == tsm2.app_results

val lemma_update_value (tsm: TSM.thread_state_model)
                       (s: T.slot {TSM.has_slot tsm s})
                       (v: T.value {T.is_value_of (TSM.key_of_slot tsm s) v})
  : Lemma (ensures (let tsm_ = TSM.update_value tsm s v in
                    identical_except_store tsm tsm_ /\
                    identical_except tsm.store tsm_.store s /\
                    inuse_slot tsm_.store s /\
                    (let Some e = get_slot tsm.store s in
                     let Some e_ = get_slot tsm_.store s in
                     e.key == e_.key /\
                     e_.value == v /\
                     e.add_method = e_.add_method /\
                     e.l_child_in_store == e_.l_child_in_store /\
                     e.r_child_in_store == e_.r_child_in_store)))

let madd_to_store_reqs (tsm: TSM.thread_state_model)
                       (s: T.slot)
                       (k: T.key)
                       (v: T.value)
                       (s':T .slot)
                       (d: bool)
  = let open TSM in
    empty_slot tsm.store s /\
    inuse_slot tsm.store s' /\
    T.is_value_of k v

val lemma_madd_to_store (tsm: TSM.thread_state_model)
                        (s: T.slot)
                        (k: T.key)
                        (v: T.value)
                        (s':T .slot)
                        (d: bool)
  : Lemma (requires (madd_to_store_reqs tsm s k v s' d))
          (ensures (let tsm_ = TSM.madd_to_store tsm s k v s' d in
                    let od = not d in
                    let open TSM in
                    identical_except_store tsm tsm_ /\
                    identical_except2 tsm.store tsm_.store s s' /\

                    // nothing changes in slot s' except it now points to s in direction d
                    inuse_slot tsm_.store s' /\
                    stored_key tsm_.store s' == stored_key tsm.store s' /\
                    stored_value tsm_.store s' == stored_value tsm.store s' /\
                    add_method_of tsm_.store s' = add_method_of tsm.store s' /\
                    points_to_dir tsm_.store s' d s /\
                    points_to_info tsm_.store s' od = points_to_info tsm.store s' od /\

                    // slot s contains (k, v, MAdd) and points to nothing
                    inuse_slot tsm_.store s /\
                    (let Some e = get_slot tsm_.store s in
                     e.key == k /\ e.value == v /\ e.add_method = MAdd /\
                     e.l_child_in_store == None /\ e.r_child_in_store == None /\
                     e.parent_slot == Some (s', d))))

let madd_to_store_split_reqs (tsm: TSM.thread_state_model)
                             (s: T.slot)
                             (k: T.key)
                             (v: T.value)
                             (s':T.slot)
                             (d d2:bool)
  = empty_slot tsm.store s /\
    inuse_slot tsm.store s' /\
    T.is_value_of k v /\
    points_to_some_slot tsm.store s' d


val lemma_madd_to_store_split (tsm: TSM.thread_state_model)
                              (s: T.slot)
                              (k: T.key)
                              (v: T.value)
                              (s':T.slot)
                              (d d2:bool)
  : Lemma (requires 
               madd_to_store_split_reqs tsm s k v s' d d2 /\
               all_props tsm.store /\
               (let tsm_ = TSM.madd_to_store_split tsm s k v s' d d2 in
                not tsm_.failed))
          (ensures (let tsm_ = TSM.madd_to_store_split tsm s k v s' d d2 in
                    let od = not d in
                    let od2 = not d2 in
                    let s2 = pointed_slot tsm.store s' d in
                    let open TSM in

                    identical_except_store tsm tsm_ /\
                    identical_except3 tsm.store tsm_.store s s' s2 /\

                    // nothing changes in slot s', except it now points to s in direction d
                    inuse_slot tsm_.store s' /\
                    stored_key tsm_.store s' == stored_key tsm.store s' /\
                    stored_value tsm_.store s' == stored_value tsm.store s' /\
                    add_method_of tsm_.store s' = add_method_of tsm.store s' /\
                    points_to_dir tsm_.store s' d s /\
                    points_to_info tsm_.store s' od = points_to_info tsm.store s' od /\

                    // slot s contains (k, v, MAdd) and points to s2 along direction d2
                    inuse_slot tsm_.store s /\
                    stored_key tsm_.store s == k /\
                    stored_value tsm_.store s == v /\
                    add_method_of tsm_.store s = MAdd /\
                    points_to_none tsm_.store s od2 /\
                    points_to_dir tsm_.store s d2 s2 /\
                    has_parent tsm_.store s /\
                    parent_slot tsm_.store s = s' /\
                    parent_dir tsm_.store s = d /\

                    inuse_slot tsm_.store s2 /\ inuse_slot tsm.store s2 /\
                    has_parent tsm_.store s2 /\
                    parent_slot tsm_.store s2 = s /\
                    parent_dir tsm_.store s2 = d2 /\

                    (let Some e = get_slot tsm.store s2 in
                     let Some e_ = get_slot tsm_.store s2 in
                     e.key == e_.key /\ e.value == e_.value /\
                     e.add_method == e_.add_method /\
                     e.l_child_in_store == e_.l_child_in_store /\
                     e.r_child_in_store == e_.r_child_in_store)))

val lemma_mevict_from_store (tsm: s_thread_state)
                            (s: T.slot)
                            (s': T.slot)
                            (d: bool)
  : Lemma (requires (s <> s' /\ TSM.has_slot tsm s'))
          (ensures (let od = not d in
                    let st = tsm.store in
                    let open TSM in
                    let tsm_ = mevict_from_store tsm s s' d in
                    let st_ = tsm_.store in

                    // st and st_ are identical except at s, s'
                    identical_except2 st st_ s s' /\

                    // slot s is empty after update
                    empty_slot st_ s /\

                    // nothing changes in slot s', except it points to none in direction d
                    inuse_slot st_ s' /\
                    stored_key st_ s' == stored_key st s' /\
                    stored_value st_ s' == stored_value st s' /\
                    add_method_of st_ s' == add_method_of st s' /\
                    points_to_info st_ s' od == points_to_info st s' od /\
                    points_to_none st_ s' d /\
                    parent_info st_ s' == parent_info st s'))

val lemma_bevict_from_store (tsm: s_thread_state)
                            (s: T.slot)
  : Lemma (ensures (let st = tsm.store in
                    let open TSM in
                    let tsm_ = bevict_from_store tsm s in
                    let st_ = tsm_.store in
                    identical_except st st_ s /\
                    empty_slot st_ s))
