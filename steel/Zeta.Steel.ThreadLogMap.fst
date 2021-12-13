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

let perm_ok (m:PM.map tid aval) (tid:tid { has_key m tid }) =
  let av = FAP.Owns?._0 (Map.sel m tid) in
  FAP.perm_ok av

let anchor_of (m:PM.map tid aval) (t:tid{ has_anchor m t }) =
  let p, _ = FAP.Owns?._0 (Map.sel m t) in
  Some?.v (snd p)

let owns_anchor_only (m:PM.map tid aval) (tid:tid) =
  has_anchor m tid /\
  None? (perm_of m tid)

let global_anchor_pred (x:t) (m:PM.map tid (option log)) (m':PM.map tid aval)
  : prop
  = forall (tid:tid). {:pattern (Map.sel m tid) \/ has_key m' tid}
       (has_key m' tid <==> Some? (Map.sel m tid)) /\
       (has_key m' tid ==>
         owns_anchor_only m' tid /\
         get m' tid == Some?.v (Map.sel m tid) /\
         anchor_of m' tid == get m' tid)

let global_anchor (x:t) ([@@@smt_fallback] m:PM.map tid (option log))
  : vprop
  = exists_ (fun m' ->
      G.pts_to x m' `star`
      pure (global_anchor_pred x m m'))

let intro_global_anchor (#o:_) (x:t) (m:PM.map tid (option log)) (m':PM.map tid aval)
  : STGhost unit o
       (G.pts_to x m')
       (fun _ -> global_anchor x m)
       (requires global_anchor_pred x m m')
       (ensures fun _ -> True)
  = intro_pure (global_anchor_pred x m m');
    intro_exists m' (fun m' ->
      G.pts_to x m' `star`
      pure (global_anchor_pred x m m'))

let global_snapshot (x:t) ([@@@smt_fallback] m: PM.map tid log)
  : vprop
  = exists_ (fun m' ->
      G.pts_to x m' `star`
      pure (forall tid. has_key m' tid /\
                   get m' tid == Map.sel m tid /\
                   no_ownership m' tid))

let tids_pts_to_pred (x:t) (frac:perm) (m:PM.map tid (option log)) (with_anchor:bool) (m': PM.map tid aval)
  : prop
  = forall (tid:tid).{:pattern (Map.sel m tid) \/ (has_key m' tid)}
           (has_key m' tid ==> Some? (Map.sel m tid)) /\
           (Some? (Map.sel m tid) ==> has_key m' tid) /\
           (has_key m' tid ==>
             perm_ok m' tid /\
             perm_of m' tid == Some frac /\
             (with_anchor <==> has_anchor m' tid) /\
             get m' tid == Some?.v (Map.sel m tid))

let tids_pts_to (x:t) ([@@@smt_fallback] frac:perm) ([@@@smt_fallback] m:PM.map tid (option log))
  : vprop
  = exists_ (fun m' ->
    G.pts_to x m' `star`
    pure (tids_pts_to_pred x frac m false m'))

let intro_tids_pts_to (#o:_) (x:t) (frac:perm) (m:PM.map tid (option log)) (m':PM.map tid aval)
  : STGhost unit o
       (G.pts_to x m')
       (fun _ -> tids_pts_to x frac m)
       (requires tids_pts_to_pred x frac m false m')
       (ensures fun _ -> True)
  = intro_pure (tids_pts_to_pred x frac m false m');
    intro_exists m' (fun m' ->
      G.pts_to x m' `star`
      pure (tids_pts_to_pred x frac m false m'))

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
    //TODO: leave out these rewrites and the tactic crashes with a scoping error
    rewrite (tids_pts_to _ _ _)
            (tids_pts_to x full_perm (Map.const (Some Seq.empty)));
    rewrite (global_anchor _ _)
            (global_anchor x (Map.const (Some Seq.empty)));
    x


let split_perm (x:FAP.avalue anchors {
                      FAP.has_nonzero (FAP.avalue_perm x) /\
                      not (FAP.has_anchor (FAP.avalue_perm x)) /\
                      FAP.perm_ok x
               })
  : y:FAP.avalue anchors { FAP.avalue_composable y y }
  = let (Some p, None), v = x in
    (Some (half_perm p), None), v

let split_ownership (frac:perm) (m:PM.map tid aval)
  : Lemma
    (requires
      forall (k:_{has_key m k}).{:pattern (Map.sel m k)}
        ~ (has_anchor m k) /\
        perm_of m k == Some frac /\
        perm_ok m k)
    (ensures
      PM.composable_maps fap
        (map_map m (fun _ -> split_perm))
        (map_map m (fun _ -> split_perm)) /\
      m `Map.equal` PM.compose_maps fap
           (map_map m (fun _ -> split_perm))
           (map_map m (fun _ -> split_perm))
      )
  = ()

let share_tids_pts_to_lemma (x:t) (f:perm) (m:PM.map tid (option log)) (m':PM.map tid aval)
  : Lemma
    (requires tids_pts_to_pred x f m false m')
    (ensures
      (forall (k:_{has_key m' k}).{:pattern (Map.sel m' k)}
        ~ (has_anchor m' k) /\
        perm_of m' k == Some f /\
        perm_ok m' k) /\
      tids_pts_to_pred x (half_perm f) m false (map_map m' (fun _ -> split_perm)))
  = ()

let share_tids_pts_to (#o:_) (#f:perm) (x:t) (m:PM.map tid (option log))
  : STGhostT unit o
    (tids_pts_to x f m)
    (fun _ -> tids_pts_to x (half_perm f) m `star` tids_pts_to x (half_perm f) m)
  = let m' : erased (PM.map tid aval) = elim_exists () in
    elim_pure _;
    split_ownership f m';
    let half_m' = map_map m' (fun _ -> split_perm) in
    G.share x m' half_m' half_m';
    share_tids_pts_to_lemma x f m m';
    intro_tids_pts_to x (half_perm f) m half_m';
    intro_tids_pts_to x (half_perm f) m half_m'

let repr_map = PM.map tid (option log)

let singleton (t:tid) (l:log)
  : repr_map
  = Map.upd (Map.const None) t (Some l)

let take_tid_lemma (x:t) (f:perm) (m:PM.map tid (option log)) (m':PM.map tid aval) (t:tid)
  : Lemma
    (requires
      Some? (Map.sel m t) /\
      tids_pts_to_pred x f m false m')
    (ensures (
      let v = Map.sel m' t in
      let m0' : PM.map _ _ = Map.upd m' t FAP.Nothing in
      let m1' : PM.map _ _ = Map.upd (Map.const FAP.Nothing) t v in
      PM.composable_maps fap m0' m1' /\
      PM.compose_maps fap m0' m1' `Map.equal` m' /\
      tids_pts_to_pred x f (Map.upd m t None) false m0' /\
      tids_pts_to_pred x f (singleton t (Some?.v (Map.sel m t))) false m1'))
  =  let v = Map.sel m' t in
     let m0' = Map.upd m' t FAP.Nothing in
     let m1' = Map.upd (Map.const FAP.Nothing) t v in
     assert (PM.composable_maps fap m0' m1');
     assert (PM.compose_maps fap m0' m1' `Map.equal` m');
     let m' : repr_map = Map.upd m t None in
     introduce forall (tid:tid).
           (has_key m0' tid <==> Some? (Map.sel m' tid)) /\
           (has_key m0' tid ==>
             perm_ok m0' tid /\
             perm_of m0' tid == Some f /\
             ~(has_anchor m0' tid) /\
             get m0' tid == Some?.v (Map.sel m' tid))
     with introduce _ /\ _
     with (())
     and (());
     assert (tids_pts_to_pred x f (Map.upd m t None) false m0')

let tid_pts_to (x:t) (t:tid) ([@@@smt_fallback] frac:perm) ([@@@smt_fallback] l:log)
  : vprop
  = tids_pts_to x frac (singleton t l)

let take_tid (#o:_) (#f:perm) (x:t) (m:PM.map tid (option log)) (t:tid { Some? (Map.sel m t) })
  : STGhostT unit o
    (tids_pts_to x f m)
    (fun _ -> tid_pts_to x t f (Some?.v (Map.sel m t)) `star`
           tids_pts_to x f (Map.upd m t None))
  = let m' : erased (PM.map tid aval) = elim_exists() in
    elim_pure _;
    take_tid_lemma x f m m' t;
    let m0' = Map.upd m' t FAP.Nothing in
    let m1' = Map.upd (Map.const FAP.Nothing) t (Map.sel m' t) in
    G.share x m' m0' m1';
    intro_tids_pts_to x f (Map.upd m t None) m0';
    let m1 : PM.map tid (option log) = singleton t (Some?.v (Map.sel m t)) in
    intro_tids_pts_to x f m1 m1';
    rewrite (tids_pts_to x f m1)
            (tid_pts_to x t f (Some?.v (Map.sel m t)))


let tid_pts_to_with_anchor (x:t) (t:tid) ([@@@smt_fallback] frac:perm) ([@@@smt_fallback] l:log)
  : vprop
  = exists_ (fun m' ->
    G.pts_to x m' `star`
    pure (tids_pts_to_pred x frac (singleton t l) true m'))

let take_anchor_tid_lemma (x:t)
                          (m0 m1:PM.map tid aval)
                          (m:PM.map tid (option log))
                          (t:tid)
                          (f:perm)
                          (l:log)
  : Lemma
    (requires
      tids_pts_to_pred x f (singleton t l) false m0 /\
      global_anchor_pred x m m1 /\
      PM.composable_maps fap m0 m1 /\
      Some? (Map.sel m t))
    (ensures (
      has_key m0 t /\
      has_key m1 t /\ (
      let FAP.Owns ((_, Some anchor), _) = Map.sel m1 t in
      let FAP.Owns (_, v) = Map.sel m0 t in
      let av' = (Some f, Some anchor), v in
      let m0' = Map.upd m0 t (FAP.Owns av') in
      let m1' = Map.upd m1 t FAP.Nothing in
      tids_pts_to_pred x f (singleton t l) true m0' /\
      global_anchor_pred x (Map.upd m t None) m1' /\
      PM.composable_maps fap m0' m1' /\
      M.committed_log_entries l == Some?.v (Map.sel m t))))
  = assert (has_key m0 t /\ has_key m1 t);
    let FAP.Owns ((_, Some anchor), _) = Map.sel m1 t in
    let FAP.Owns (_, v) = Map.sel m0 t in
    let av' = (Some f, Some anchor), v in
    let m0' = Map.upd m0 t (FAP.Owns av') in
    let m1' = Map.upd m1 t FAP.Nothing in
    assert (PM.composable_maps fap m0' m1');
    introduce forall (tid:tid).
           (has_key m0' tid <==> Some? (Map.sel (singleton t l) tid)) /\ True
           // (has_key m0' tid ==>
           //   perm_ok m0' tid /\
           //   perm_of m0' tid == Some f /\
           //   (has_anchor m0' tid) /\
           //   get m0' tid == Some?.v (Map.sel (singleton t l) tid))
    with introduce _ /\ _
    with (())
    and (());
    assert (tids_pts_to_pred x f (singleton t l) true m0');
    introduce forall (tid:tid).
       (has_key m1' tid <==> Some? (Map.sel (Map.upd m t None) tid)) /\ True
       // (has_key m1' tid ==>
       //   owns_anchor_only m1' tid /\
       //   get m1' tid == Some?.v (Map.sel (Map.upd m t None) tid) /\
       //   anchor_of m1' tid == get m1' tid)
    with introduce _ /\ _
    with (())
    and (());
    assert (global_anchor_pred x (Map.upd m t None) m1')

let elim_tids_pts_to (#o:_) (x:t) (frac:perm) (m:PM.map tid (option log))
  : STGhost (erased (PM.map tid aval)) o
       (tids_pts_to x frac m)
       (fun m' -> G.pts_to x m')
       (requires True)
       (ensures fun m' -> tids_pts_to_pred x frac m false m')
  = let m' = elim_exists () in
    elim_pure _;
    m'

let elim_global_anchor (#o:_) (x:t) (m:PM.map tid (option log))
  : STGhost (erased (PM.map tid aval)) o
       (global_anchor x m)
       (fun m' -> G.pts_to x m')
       (requires True)
       (ensures fun m' -> global_anchor_pred x m m')
  = let m' = elim_exists () in
    elim_pure _;
    m'

let gpts_to_composable (#o:_) (x:t) (m0 m1:PM.map tid aval)
  : STGhost unit o
    (G.pts_to x m0 `star` G.pts_to x m1)
    (fun _ -> G.pts_to x m0 `star` G.pts_to x m1)
    (requires True)
    (ensures fun _ -> PM.composable_maps fap m0 m1)
 = let _ = G.gather x m0 m1 in
   G.share x _ m0 m1

let take_anchor_tid (#o:_) (x:t) (m:PM.map tid (option log))
                           (t:tid) (f:perm) (l:log)
  : STGhost unit o
    (tid_pts_to x t f l `star` global_anchor x m)
    (fun _ -> tid_pts_to_with_anchor x t f l `star`
           global_anchor x (Map.upd m t None))
    (requires
      Some? (Map.sel m t))
    (ensures fun _ ->
      Some? (Map.sel m t) /\
      M.committed_log_entries l == Some?.v (Map.sel m t))
  = let m0 = elim_tids_pts_to x f _ in
    let m1 = elim_global_anchor x m in
    gpts_to_composable x m0 m1;
    take_anchor_tid_lemma x m0 m1 m t f l;
    let FAP.Owns ((_, Some anchor), _) = Map.sel m1 t in
    let FAP.Owns (_, v) = Map.sel m0 t in
    let av' = (Some f, Some anchor), v in
    let m0' = Map.upd m0 t (FAP.Owns av') in
    let m1' = Map.upd m1 t FAP.Nothing in
    admit_()
    // intro_tids_pts_to x f
    //   tids_pts_to_pred x f (singleton t l) true m0' /\
    //   global_anchor_pred x (Map.upd m t None) m1' /\
    //   PM.composable_maps fap m0' m1' /\
    //   M.committed_log_entries l == Some?.v (Map.sel m t)
    // admit_()


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
