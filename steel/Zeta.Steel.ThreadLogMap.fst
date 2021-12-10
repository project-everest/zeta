module Zeta.Steel.ThreadLogMap
open FStar.Ghost
open FStar.Seq
open Zeta.Steel.FormatsManual
open Zeta.Steel.ApplicationTypes
open Zeta.Steel.ApplicationTypes
open Steel.ST.Util
module FAP = Zeta.Steel.FractionalAnchoredPreorder
module PM = Zeta.Steel.PCMMap
module M = Zeta.Steel.ThreadStateModel

let log = Seq.seq log_entry_base

let log_grows :Preorder.preorder log
  = let open FStar.Seq in
    fun (s1 s2:log) ->
      length s1 <= length s2 /\
      (forall (i:nat).{:pattern (Seq.index s1 i) \/ (Seq.index s2 i)}
         i < length s1 ==> index s1 i == index s2 i)

let committed_log_entries_split (l0 l1 l2: log)
  : Lemma
    (requires
      M.committed_log_entries l0 == M.committed_log_entries l2 /\
      log_grows l0 l1 /\
      log_grows l1 l2)
    (ensures
            M.committed_log_entries l0 == M.committed_log_entries l1)
  = admit()


let anchor : log -> log -> prop
  = fun l0 l1 ->
      log_grows l0 l1 /\
      M.committed_log_entries l0 == M.committed_log_entries l1

let anchor_refl : squash (forall l. anchor l l) = ()
let anchor_pre : squash (forall l0 l1. anchor l0 l1 ==> log_grows l0 l1) = ()
let anchor_split : squash (forall x z. x `anchor` z  ==> (forall y. log_grows x y /\ log_grows y z ==> x `anchor` y)) =
  introduce forall x. _
  with introduce forall z. x `anchor` z  ==> (forall y. log_grows x y /\ log_grows y z ==> x `anchor` y)
  with introduce _ ==> _
  with _. introduce forall y. _
  with introduce _ ==> _
  with _. committed_log_entries_split x y z
let anchors : FAP.anchor_rel log_grows = anchor

let fap = FAP.pcm #log #log_grows #anchors
let pcm = PM.pointwise tid fap
let aval = FAP.knowledge anchors
let has_key  (m:PM.map tid aval) (tid:tid) = FAP.Owns? (Map.sel m tid)
let owns_key (m:PM.map tid aval) (tid:tid) =
  has_key m tid /\
  FAP.avalue_owns (FAP.Owns?._0 (Map.sel m tid))
let avalue_of (m:PM.map tid aval) (tid:tid { has_key m tid }) =
  (FAP.Owns?._0 (Map.sel m tid))
let get (m:PM.map tid aval) (tid:tid { has_key m tid }) =
  Steel.Preorder.curval (FAP.avalue_val (avalue_of m tid))
let put (m:PM.map tid aval) (tid:tid { has_key m tid }) (l:log {get m tid `log_grows` l}) =
  Map.upd m tid (FAP.Owns (FAP.avalue_update_value (FAP.Owns?._0 (Map.sel m tid)) l))

let update_value (l:log)
                 (m:PM.map tid aval)
                 (tid:tid {
                   owns_key m tid /\ //if you have full ownership of key
                   get m tid `log_grows` l //you can update it wrt the preorder only
                 })
  : PCM.frame_preserving_upd pcm m (put m tid l)
  = PM.lift_fp_upd _ _ (FAP.update_value (FAP.Owns?._0 (Map.sel m tid)) l) m tid

let owns_anchored_key (m:PM.map tid aval) (tid:tid) =
  has_key m tid /\
  FAP.avalue_owns_anchored (FAP.Owns?._0 (Map.sel m tid))

let put_anchored (m:PM.map tid aval)
                 (tid:tid { has_key m tid })
                 (l:log {
                   get m tid `log_grows` l /\
                   l `FAP.compat_with_any_anchor_of` (avalue_of m tid)
                 }) =
  Map.upd m tid (FAP.Owns (FAP.avalue_update_anchored_value (FAP.Owns?._0 (Map.sel m tid)) l))

let update_anchored_value (l:log)
                          (m:PM.map tid aval)
                          (tid:tid {
                            owns_anchored_key m tid /\ //if you own an anchored key, you can update if you respect
                            get m tid `log_grows` l /\ //the preorder
                            l `FAP.compat_with_any_anchor_of` (avalue_of m tid) //and respect any anchor of the current value
                          })
  : PCM.frame_preserving_upd pcm m (put_anchored m tid l)
  = PM.lift_fp_upd _ _ (FAP.update_anchored_value (FAP.Owns?._0 (Map.sel m tid)) l) m tid
