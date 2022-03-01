module Zeta.Steel.AddMRel

open Zeta.Steel.KeyUtils
open Zeta.Steel.ThreadStateModel
open Zeta.Steel.Rel
open Zeta.Steel.StoreRel
open Zeta.Steel.ThreadRelDef

module LT = Zeta.Steel.LogEntry.Types
module T = Zeta.Steel.FormatsManual
module SS = Zeta.Steel.StoreRel
module IV = Zeta.Intermediate.Verifier

(* steel-level addm param *)
noeq type addm_param =
  | AMP: s: s_slot_id ->
          p: s_record ->
          s': s_slot_id ->
          vs': s_thread_state -> addm_param

let addm_precond0 (a: addm_param)
  = match a with
    | AMP s p s' _ ->
    check_slot_bounds s /\
    check_slot_bounds s'

(* the key being added *)
let addm_key (a: addm_param {addm_precond0 a})
  = let AMP _ (gk,gv) _ _ = a in
    gk

let addm_base_key (a: addm_param {addm_precond0 a})
  = to_base_key (addm_key a)

(* slot where the record is being added *)
let addm_slot (a: addm_param) =
  match a with
  | AMP s _ _ _ -> s

(* the slot where the ancestore record is stored *)
let addm_anc_slot (a: addm_param) =
  match a with
  | AMP _ _ s' _ -> s'

(* the state of the store before the add *)
let addm_store_pre (a: addm_param) =
  match a with
  | AMP _ _ _ vs' ->  vs'.store

(* initial set of addm preconditions: vaddm fails if these are not met *)
let addm_precond1 (a: addm_param) =
  let st' = addm_store_pre a in
  let s = addm_slot a in
  let s' = addm_anc_slot a in
  addm_precond0 a /\
  s <> s' /\
  inuse_slot st' s' /\
  empty_slot st' s /\
  (let k' = stored_base_key st' s' in
   let gk = addm_key a in
   is_proper_descendent (to_base_key gk) k')

let addm_value_pre (a: addm_param {addm_precond1 a})  =
  match a with
  | AMP _ (gk,gv) _ _ -> gv

let addm_hash_val_pre (a: addm_param {addm_precond1 a}) =
  Zeta.Steel.HashValue.hashfn (addm_value_pre a)

let addm_anc_key (a: addm_param {addm_precond1 a}): GTot (T.internal_key) =
  stored_base_key (addm_store_pre a) (addm_anc_slot a)

let addm_anc_val_pre (a: addm_param {addm_precond1 a}) =
  let st' = addm_store_pre a in
  let s' = addm_anc_slot a in
  let Some mv = to_merkle_value (stored_value st' s') in
  mv

let addm_dir (a: addm_param {addm_precond1 a}) =
  desc_dir (addm_base_key a) (addm_anc_key a)

let mv_points_to_none (mv: T.mval_value) (d: bool)
  = desc_hash_dir mv d = T.Dh_vnone ()

let mv_points_to_some (v:T.mval_value) (d:bool): bool =
  T.Dh_vsome? (desc_hash_dir v d)

let mv_pointed_key (v:T.mval_value) (d: bool{mv_points_to_some v d}): T.base_key =
  let T.Dh_vsome dh = desc_hash_dir v d in
  dh.dhd_key

let mv_pointed_hash (v:T.mval_value) (d: bool{mv_points_to_some v d}): T.hash_value =
  let T.Dh_vsome dh = desc_hash_dir v d in
  dh.dhd_h

let mv_points_to (v:T.mval_value) (d:bool) (k:T.base_key): bool =
  mv_points_to_some v d && mv_pointed_key v d = k

let mv_evicted_to_blum (v: T.mval_value) (d: bool {mv_points_to_some v d})
  = let T.Dh_vsome dh = desc_hash_dir v d in
    dh.evicted_to_blum = T.Vtrue

let addm_precond2 (a: addm_param) =
  addm_precond1 a /\
  (let mv' = addm_anc_val_pre a in
   let d = addm_dir a in
   mv_points_to_none mv' d \/                          // case A: ancestor points to nothing along d
   mv_points_to mv' d (addm_base_key a) \/                  // case B: ancestor points to key being added
   is_proper_descendent (mv_pointed_key mv' d) (addm_base_key a)) // case C: ancestor points to some key below key being added

// case A:
let addm_anc_points_null (a: addm_param {addm_precond2 a}) =
  mv_points_to_none (addm_anc_val_pre a) (addm_dir a)

// case B:
let addm_anc_points_to_key (a: addm_param {addm_precond2 a}) =
  mv_points_to (addm_anc_val_pre a) (addm_dir a) (addm_base_key a)

// desc hash at ancestor along addm direction
let addm_desc_hash_dir (a: addm_param {addm_precond2 a /\ addm_anc_points_to_key a}) =
  desc_hash_dir (addm_anc_val_pre a) (addm_dir a)

// case C:
let addm_anc_points_to_desc (a: addm_param {addm_precond2 a}) =
  let mv' = addm_anc_val_pre a in
  let d = addm_dir a in
  mv_points_to_some mv' d /\
  is_proper_descendent (mv_pointed_key mv' d) (addm_base_key a)

// desc key for case C:
let addm_desc (a:addm_param {addm_precond2 a /\ addm_anc_points_to_desc a}):
  GTot (k2: T.base_key {is_proper_descendent k2 (addm_base_key a)}) =
  mv_pointed_key (addm_anc_val_pre a) (addm_dir a)

let addm_desc_dir (a: addm_param {addm_precond2 a /\ addm_anc_points_to_desc a})
  : GTot bool
  = desc_dir (addm_desc a) (addm_base_key a)

let addm_precond (a: addm_param) =
  let st = addm_store_pre a in
  let s' = addm_anc_slot a in
  addm_precond2 a /\
  (let d = addm_dir a in
   (addm_anc_points_null a ==> (addm_value_pre a = init_value (addm_key a) /\
                              points_to_none st s' d)) /\
   (addm_anc_points_to_key a ==> (addm_desc_hash_dir a = T.Dh_vsome ({ dhd_key = (addm_base_key a);
                                                                    dhd_h = (addm_hash_val_pre a);
                                                                    evicted_to_blum = T.Vfalse })) /\
                                points_to_none st s' d) /\
   (addm_anc_points_to_desc a ==> (addm_value_pre a = init_value (addm_key a))))

(* does the ancestor point to the descendant slot *)
let addm_has_desc_slot (a: addm_param {addm_precond a}) =
  addm_anc_points_to_desc a /\
  (let s' = addm_anc_slot a in
   let st' = addm_store_pre a in
   let d = addm_dir a in
   SS.points_to_some_slot st' s' d)

let addm_desc_slot (a: addm_param {addm_precond a /\ addm_has_desc_slot a}) =
  let s' = addm_anc_slot a in
  let st' = addm_store_pre a in
  let d = addm_dir a in
  pointed_slot st' s' d

let addm_value_postcond (a: addm_param {addm_precond a})
  (v: T.value {LT.is_value_of (addm_key a) v}) =
  (addm_anc_points_null a /\ (v = addm_value_pre a)) \/
  (addm_anc_points_to_key a /\ (v = addm_value_pre a)) \/
  (addm_anc_points_to_desc a /\
    (let dd = addm_desc_dir a in
     let odd = not dd in
     let Some mv = to_merkle_value v in
     desc_hash_dir mv dd = desc_hash_dir (addm_anc_val_pre a) (addm_dir a) /\
     desc_hash_dir mv odd = T.Dh_vnone ()))

let addm_slot_points_postcond (a: addm_param {addm_precond a}) (st: contents) =
  let s = addm_slot a in
  let st' = addm_store_pre a in
  let s' = addm_anc_slot a in
  let d = addm_dir a in
  inuse_slot st s /\
  ((addm_anc_points_null a /\ points_to_none st s true /\ points_to_none st s false) \/
   (addm_anc_points_to_key a /\ points_to_none st s true /\ points_to_none st s false) \/
   (addm_anc_points_to_desc a /\ (points_to_info st s (addm_desc_dir a) = points_to_info st' s' d) /\
                                 points_to_none st s (not (addm_desc_dir a))))

(* post-condition on addm slot *)
let addm_slot_postcond (a: addm_param {addm_precond a}) (st: contents) =
  let s = addm_slot a in
  inuse_slot st s  /\                          // in use
  stored_key st s = addm_key a   /\            // stores key k
  add_method_of st s = MAdd /\            // stores the correct add method
  addm_value_postcond a (stored_value st s) /\ // value postcond
  addm_slot_points_postcond a st /\
  has_parent st s /\
  parent_slot st s = addm_anc_slot a /\
  parent_dir st s = addm_dir a

let addm_anc_val_postcond (a: addm_param {addm_precond a}) (mv: T.mval_value) =
  let mv' = addm_anc_val_pre a in
  let d = addm_dir a in
  let od = not d in
  desc_hash_dir mv od = desc_hash_dir mv' od /\               // merkle value unchanged in other direction
  mv_points_to mv d (addm_base_key a) /\          // merkle value points to k in addm direction
  mv_evicted_to_blum mv d = false /\
  mv_pointed_hash mv d =
    (if (addm_anc_points_to_key a) then
      mv_pointed_hash mv' d
    else
      zero)

let addm_anc_slot_points_postcond (a: addm_param {addm_precond a}) (st: contents) =
  let st' = addm_store_pre a in
  let s' = addm_anc_slot a in
  let d = addm_dir a in
  let od = not d in
  inuse_slot st s' /\
  points_to_info st s' od = points_to_info st' s' od /\        // points to does not change in other dir
  points_to_dir st s' d (addm_slot a)

let addm_anc_slot_postcond (a: addm_param {addm_precond a}) (st: contents) =
  let s' = addm_anc_slot a in
  let st' = addm_store_pre a in
  inuse_slot st s' /\
  stored_base_key st s' = addm_anc_key a /\
  add_method_of st s' = add_method_of st' s' /\
  addm_anc_val_postcond a (Some?. v (to_merkle_value (stored_value st s'))) /\
  addm_anc_slot_points_postcond a st /\
  (let Some e' = get_slot st' s' in
   let Some e = get_slot st s' in
   e.parent_slot = e'.parent_slot)

let addm_desc_slot_postcond (a: addm_param {addm_precond a /\ addm_has_desc_slot a}) (st: contents) =
  let sd = addm_desc_slot a in
  let st' = addm_store_pre a in
  inuse_slot st sd /\ inuse_slot st' sd /\
  stored_key st sd = stored_key st' sd /\
  stored_value st sd = stored_value st' sd /\
  add_method_of st sd = add_method_of st' sd /\
  has_parent st sd /\
  parent_slot st sd = addm_slot a /\
  parent_dir st sd = addm_desc_dir a /\
  points_to_info st sd true = points_to_info st' sd true /\
  points_to_info st sd false = points_to_info st' sd false

let addm_postcond (a: addm_param {addm_precond a}) (vs: s_thread_state) =
  let vs' = a.vs' in

  (vs.failed = vs'.failed /\
   vs.thread_id = vs'.thread_id /\ vs.clock = vs'.clock /\                // everything except store is unchanged
   (addm_has_desc_slot a /\
    identical_except3 vs.store vs'.store (addm_slot a) (addm_anc_slot a) (addm_desc_slot a) /\
    addm_desc_slot_postcond a vs.store
    \/
    ~ (addm_has_desc_slot a) /\
    identical_except2 vs.store vs'.store (addm_slot a) (addm_anc_slot a)) /\
   addm_slot_postcond a vs.store /\                                      // postcond on slot s
   addm_anc_slot_postcond a vs.store)                                    // postcond on slot s'

let i_addm_param = IV.addm_param i_vcfg

let related_addm_param (a: addm_param) (i_a: i_addm_param)
  = let AMP _ _ _ tsm = a in
    let IV.AMP _ _ _ i_tsm = i_a in
    addm_precond0 a /\
    related_slot (addm_slot a) (IV.addm_slot i_a) /\
    related_slot (addm_anc_slot a) (IV.addm_anc_slot i_a) /\
    related_tsm tsm i_tsm /\
    related_key (addm_key a) (IV.addm_key i_a) /\
    (addm_precond1 a ==> IV.addm_precond1 i_a ==>
     related_val (addm_value_pre a)  (IV.addm_value_pre i_a))

val related_addm_precond (a: addm_param) (i_a: i_addm_param)
  : Lemma (requires (related_addm_param a i_a /\ addm_precond a))
          (ensures (IV.addm_precond i_a))
          [SMTPat (related_addm_param a i_a)]

val related_addm_postcond (a: addm_param) (i_a: i_addm_param) (tsm_: s_thread_state) (i_tsm_: i_thread_state)
  : Lemma (requires (related_addm_param a i_a /\ addm_precond a /\
                     addm_postcond a tsm_ /\
                     IV.addm_postcond i_a i_tsm_))
          (ensures (related_tsm tsm_ i_tsm_))
