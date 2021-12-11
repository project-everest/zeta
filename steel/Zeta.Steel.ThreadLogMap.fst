module Zeta.Steel.ThreadLogMap
open FStar.Ghost
open FStar.Seq
open Zeta.Steel.FormatsManual
open Zeta.Steel.ApplicationTypes
open Zeta.Steel.ApplicationTypes
open Steel.ST.Util
module FAP = Steel.FractionalAnchoredPreorder
module PM = Steel.PCMMap
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
      l0 == M.committed_log_entries l2 /\
      log_grows l0 l1 /\
      log_grows l1 l2)
    (ensures
      l0 == M.committed_log_entries l1)
  = admit()


let anchor : log -> log -> prop
  = fun l0 l1 ->
      log_grows l0 l1 /\
      l0 == M.committed_log_entries l1

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
let put (m:PM.map tid aval)
        (tid:tid { has_key m tid })
        (l:log {get m tid `log_grows` l /\ anchors l l})
  = Map.upd m tid (FAP.Owns (FAP.avalue_update_value (FAP.Owns?._0 (Map.sel m tid)) l))

let update_value (l:log)
                 (m:PM.map tid aval)
                 (tid:tid {
                   owns_key m tid /\ //if you have full ownership of key
                   get m tid `log_grows` l /\ //you can update it wrt the preorder only
                   anchors l l
                 })
  : PCM.frame_preserving_upd pcm m (put m tid l)
  = PM.lift_frame_preserving_upd _ _ (FAP.update_value (FAP.Owns?._0 (Map.sel m tid)) l) m tid

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
  = PM.lift_frame_preserving_upd _ _ (FAP.update_anchored_value (FAP.Owns?._0 (Map.sel m tid)) l) m tid

// // ////////////////////////////////////////////////////////////////////////////////

// // let tmap (k:eqtype) (v:Type0) (c:preorder v) = Map.t k (hist c)
module G = Steel.ST.GhostPCMReference

let t = G.ref _ pcm

let no_ownership (m:PM.map tid aval) (tid:tid) =
  not (has_key m tid) \/
  (let (p, _) = FAP.Owns?._0 (Map.sel m tid) in
   None? (fst p) /\
   None? (snd p))

let has_anchor (m:PM.map tid aval) (tid:tid) =
  has_key m tid /\
  (let p, _ = FAP.Owns?._0 (Map.sel m tid) in
   Some? (snd p))

let perm_of (m:PM.map tid aval) (tid:tid { has_key m tid }) =
  let p, _ = FAP.Owns?._0 (Map.sel m tid) in
  fst p

let anchor_of (m:PM.map tid aval) (t:tid{ has_anchor m t }) =
  let p, _ = FAP.Owns?._0 (Map.sel m t) in
  Some?.v (snd p)

let owns_anchor_only (m:PM.map tid aval) (tid:tid) =
  has_anchor m tid /\
  None? (perm_of m tid)

let global_anchor_pred (x:t) (m:PM.map tid (option log)) (m':PM.map tid aval)
  : prop
  = forall tid.
      match Map.sel m tid with
      | None ->
        not (has_key m' tid)
      | Some l ->
        owns_anchor_only m' tid /\
        get m' tid == l /\
        anchor_of m' tid == l

assume
val global_anchor (x:t) ([@@@smt_fallback] m:PM.map tid (option log))
  : vprop
  // = exists_ (fun m' ->
  //     G.pts_to x m' `star`
  //     pure (global_anchor_pred x m m'))

let intro_global_anchor (#o:_) (x:t) (m:PM.map tid (option log)) (m':PM.map tid aval)
  : STGhost unit o
       (G.pts_to x m')
       (fun _ -> global_anchor x m)
       (requires global_anchor_pred x m m')
       (ensures fun _ -> True)
  = admit_()
    // intro_pure (global_anchor_pred x m m');
    // intro_exists m' (fun m' ->
    //   G.pts_to x m' `star`
    //   pure (global_anchor_pred x m m'))

let global_snapshot (x:t) ([@@@smt_fallback] m: PM.map tid log)
  : vprop
  = exists_ (fun m' ->
      G.pts_to x m' `star`
      pure (forall tid. has_key m' tid /\
                   get m' tid == Map.sel m tid /\
                   no_ownership m' tid))

let tid_pts_to (x:t)
               (tid:tid)
               ([@@@smt_fallback] frac:perm)
               ([@@@smt_fallback]  l:log) =
  exists_ (fun m ->
    G.pts_to x m `star`
    pure (forall t. if t=tid
               then (
                 has_key m t /\
                 perm_of m tid == Some frac /\
                 ~ (has_anchor m tid) /\
                 get m t == l
               )
               else (
                 not (has_key m t)
               )))

let tids_pts_to_pred (x:t) (frac:perm) (m:PM.map tid (option log)) (m': PM.map tid aval)
  : prop
  = forall tid.
      match Map.sel m tid with
      | None -> not (has_key m' tid)
      | Some l ->
        has_key m' tid /\
        perm_of m' tid == Some frac /\
        get m' tid == l /\
        ~ (has_anchor m' tid)

assume
val tids_pts_to (x:t) ([@@@smt_fallback] frac:perm) ([@@@smt_fallback] m:PM.map tid (option log))
  : vprop
  // exists_ (fun m' ->
  //   G.pts_to x m' `star`
  //   pure (tids_pts_to_pred x frac m m'))

let intro_tids_pts_to (#o:_) (x:t) (frac:perm) (m:PM.map tid (option log)) (m':PM.map tid aval)
  : STGhost unit o
       (G.pts_to x m')
       (fun _ -> tids_pts_to x frac m)
       (requires tids_pts_to_pred x frac m m')
       (ensures fun _ -> True)
  = intro_pure (tids_pts_to_pred x frac m m');
    intro_exists m' (fun m' ->
      G.pts_to x m' `star`
      pure (tids_pts_to_pred x frac m m'));
    admit_()

let alloc0 (#o:_) (_:unit)
  : STGhostT t o
             emp
             (fun t -> G.pts_to t (Map.const (FAP.Owns (FAP.initial_value Seq.empty))))
  = G.alloc (Map.const (FAP.Owns (FAP.initial_value Seq.empty)))

let map_map (m:PM.map tid aval)
            (f:(tid:tid -> a:FAP.avalue anchors{ Map.sel m tid == FAP.Owns a } -> FAP.avalue anchors))
  : PM.map tid aval
  = Map.map_literal (fun tid ->
       match Map.sel m tid with
       | FAP.Owns m -> FAP.Owns (f tid m)
       | FAP.Nothing -> FAP.Nothing)

let split_anchor (m:PM.map tid aval)
  : Lemma
    (requires
      forall (k:_{has_key m k}).{:pattern (Map.sel m k)}
        anchors (get m k) (get m k) /\
        owns_key m k)
    (ensures
      PM.composable_maps fap
        (map_map m (fun _ a -> fst (FAP.anchored_snapshot a)))
        (map_map m (fun _ a -> snd (FAP.anchored_snapshot a))) /\
      m `Map.equal` PM.compose_maps fap
           (map_map m (fun _ a -> fst (FAP.anchored_snapshot a)))
           (map_map m (fun _ a -> snd (FAP.anchored_snapshot a)))
      )
  = ()

let alloc (#o:_) (_:unit)
  : STGhostT t o
             emp
             (fun t -> tids_pts_to t full_perm (Map.const (Some Seq.empty)) `star`
                    global_anchor t (Map.const (Some Seq.empty)))
  = let m = (Map.const (FAP.Owns (FAP.initial_value Seq.empty))) in
    let x = alloc0 () in
    rewrite (G.pts_to x _)
            (G.pts_to x m);
    split_anchor m;
    let m0 = map_map m (fun _ a -> fst (FAP.anchored_snapshot a)) in
    let m1 = map_map m (fun _ a -> snd (FAP.anchored_snapshot a)) in
    G.share x m m0 m1;
    assert_ (G.pts_to x m0 `star` G.pts_to x m1);
    let mm0 : PM.map tid (option log) = Map.const (Some Seq.empty) in
    intro_tids_pts_to x full_perm mm0 m0;
    intro_global_anchor x mm0 m1;
    x


let share_tid_pts_to (#o:_) (#f:perm) (x:t) (m:PM.map tid (option log))
  : STGhostT unit o
    (tids_pts_to x f m)
    (fun _ -> tids_pts_to x (half_perm f) m `star` tids_pts_to x (half_perm f) m)
  = admit_()

let take_tid (#o:_) (#f:perm) (x:t) (m:PM.map tid (option log)) (tid:tid { Some? (Map.sel m tid) })
  : STGhostT unit o
    (tids_pts_to x f m)
    (fun _ -> tid_pts_to x tid f (Some?.v (Map.sel m tid)) `star`
           tids_pts_to x (half_perm f) (Map.upd m tid None))
  = admit_()





//                perm_ok (Map.sel m t)))

// val global_snapshot (x:t) (m:map tid log)
//   : vprop
//   = G.pts_to x m `star`
//   exists_ (fun (km:kmap k v c) ->
//         pure (snapshot km == m) `star`
//         k_of t (Owns (ksnapshot km)))

// // // val k_of (#k:eqtype) (#v:Type0) (#c:preorder v)
// // //          (t:t k v c)
// // //          (knowledge: knowledge k v c)
// // //   : vprop

// // // val share  (#o:_)
// // //            (#k:eqtype) (#v:Type0) (#c:preorder v)
// // //            (#m0 :kmap k v c)
// // //            (#m1: kmap k v c { kmap_composable m0 m1 })
// // //            (t:t k v c)
// // //   : STGhostT unit o
// // //     (k_of t (Owns (compose_kmaps m0 m1)))
// // //     (fun _ -> k_of t (Owns m0) `star` k_of t (Owns m1))

// // // val gather (#o:_)
// // //            (#k:eqtype) (#v:Type0) (#c:preorder v)
// // //            (#m0 #m1: kmap k v c)
// // //            (t:t k v c)
// // //   : STGhostT (_:unit { kmap_composable m0 m1 }) o
// // //     (k_of t (Owns m0) `star` k_of t (Owns m1))
// // //     (fun _ -> k_of t (Owns (compose_kmaps m0 m1)))


// // // val take_snapshot (#o:_)
// // //                   (#k:eqtype) (#v:Type0) (#c:preorder v)
// // //                   (#m: kmap k v c)
// // //                   (t:t k v c)
// // //   : STGhostT unit o
// // //     (k_of t (Owns m))
// // //     (fun _ -> k_of t (Owns m) `star` global_snapshot t (snapshot m))

// // // val owns_key (#k:eqtype) (#v:Type0) (#c:preorder v)
// // //              (t:t k v c)
// // //              (key:k)
// // //              ([@@@smt_fallback]perm:perm)
// // //              ([@@@smt_fallback]value:v)
// // //  : vprop
// // //   // = exists_ (fun (m:kmap k v c) ->
// // //   //      pure ((forall key'. (key<>key' ==> fst (Map.sel m key') == None)) /\
// // //   //            (match Map.sel m key with
// // //   //             | None, _ -> False
// // //   //             | Some p, h ->
// // //   //               perm == p /\
// // //   //               curval h == value)) `star`
// // //   //      k_of t (Owns m))

// // // val snapshot_of_key (#k:eqtype) (#v:Type0) (#c:preorder v)
// // //                     (t:t k v c)
// // //                     (key:k)
// // //                     ([@@@smt_fallback]value:v)
// // //  : vprop
// // //   // = exists_ (fun (m:kmap k v c) ->
// // //   //      pure ((forall key'. fst (Map.sel m key') == None) /\
// // //   //            (match Map.sel m key with
// // //   //             | Some _, _ -> False
// // //   //             | None, h -> curval h == value)) `star`
// // //   //      k_of t (Owns m))

// // // val local_snapshot (#o:_)
// // //                    (#k:eqtype) (#v:Type0) (#c:preorder v)
// // //                    (#key:k) (#frac:_) (#value:v)
// // //                    (t:t k v c)
// // //   : STGhostT unit o
// // //     (owns_key t key frac value)
// // //     (fun _ -> owns_key t key frac value `star` snapshot_of_key t key value)

// // // val dup_snapshot (#o:_)
// // //                  (#k:eqtype) (#v:Type0) (#c:preorder v)
// // //                  (#key:k) (#value:v)
// // //                  (t:t k v c)
// // //   : STGhostT unit o
// // //     (snapshot_of_key t key value)
// // //     (fun _ -> snapshot_of_key t key value `star` snapshot_of_key t key value)

// // // val update (#o:_)
// // //            (#k:eqtype) (#v:Type0) (#c:preorder v)
// // //            (#key:k) (#value:v)
// // //            (t:t k v c)
// // //            (value':v {c value value'})
// // //   : STGhostT unit o
// // //     (owns_key t key full_perm value)
// // //     (fun _ -> owns_key t key full_perm value')

// // // val update_global_snapshot (#o:_)
// // //                            (#k:eqtype) (#v:Type0) (#c:preorder v)
// // //                            (#key:k) (#frac:_) (#value:v)
// // //                            (t:t k v c)
// // //                            (m:Map.t k v)
// // //   : STGhostT unit o
// // //     (owns_key t key frac value `star` global_snapshot t m)
// // //     (fun _ -> owns_key t key frac value `star` global_snapshot t (Map.upd m key value))


// // // val dup_global_snapshot (#o:_) (#k:eqtype) (#v:Type0) (#c:preorder v) (#m: Map.t k v)
// // //                         (t:t k v c)
// // //   : STGhostT unit o
// // //     (global_snapshot t m)
// // //     (fun _ -> global_snapshot t m `star` global_snapshot t m)
