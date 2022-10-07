module Zeta.Steel.ThreadLogMap
open FStar.Ghost
open FStar.Seq
open Zeta.Steel.FormatsManual
open Zeta.Steel.ApplicationTypes
open Steel.ST.Util
module FAP = Steel.FractionalAnchoredPreorder
module PM = Steel.PCMMap
module M = Zeta.Steel.ThreadStateModel
module SA = Zeta.SeqAux

let committed_log_entries_split (l0 l1 l2: log)
  : Lemma
    (requires
      l0 == M.committed_log_entries l2 /\
      log_grows l0 l1 /\
      log_grows l1 l2)
    (ensures
      l0 == M.committed_log_entries l1)
  = let is_verify_epoch = function VerifyEpoch -> true | _ -> false in
    if SA.exists_sat_elems is_verify_epoch l2
    then (
      let i = SA.last_index is_verify_epoch l2 in
      assert (i < Seq.length l1);
      introduce forall j. i < j /\ j < Seq.length l1 ==>
                     not (is_verify_epoch (Seq.index l1 j))
      with introduce _ ==> _
      with _ . SA.lemma_last_index_correct1 is_verify_epoch l2 j;
      SA.last_index_opt_elim is_verify_epoch l1;
      assert (SA.prefix l1 (i + 1) `Seq.equal` SA.prefix l2 (i + 1));
      assert (SA.prefix l2 (i + 1) == l0)
    )
    else (
      assert (l0 == Seq.empty);
      assert (l1 `Seq.equal` SA.prefix l2 (Seq.length l1));
      assert (SA.is_prefix l2 l1);
      SA.lemma_not_exists_prefix is_verify_epoch l2 (Seq.length l1)
    )

let anchor : log -> log -> prop
  = fun l0 l1 ->
      log_grows l0 l1 /\
      l0 == M.committed_log_entries l1

let anchor_pre : squash (forall l0 l1. anchor l0 l1 ==> log_grows l0 l1) = ()

let anchor_split
  : squash (forall x z. x `anchor` z  ==> (forall y. log_grows x y /\ log_grows y z ==> x `anchor` y))
  = introduce forall x. _
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


(*** Ownership predicates ***)
let related_domains (m:repr) (m':PM.map tid aval) =
    forall tid. has_key m' tid <==> Some? (Map.sel m tid)

let global_anchor_pred (x:t) (m:repr) (m':PM.map tid aval)
  : prop
  = related_domains m m' /\
    (forall (tid:tid). {:pattern (Map.sel m tid) \/ has_key m' tid}
       (has_key m' tid ==>
         owns_anchor_only m' tid /\
         get m' tid == Some?.v (Map.sel m tid) /\
         anchor_of m' tid == get m' tid))

let global_anchor (x:t) ([@@@smt_fallback] m:repr)
  : vprop
  = exists_ (fun m' ->
      G.pts_to x m' `star`
      pure (global_anchor_pred x m m'))


let intro_global_anchor (#o:_)
                        (x:t)
                        (m:repr) (m':PM.map tid aval)
  : STGhost unit o
       (G.pts_to x m')
       (fun _ -> global_anchor x m)
       (requires global_anchor_pred x m m')
       (ensures fun _ -> True)
  = intro_pure (global_anchor_pred x m m');
    intro_exists m' (fun m' ->
      G.pts_to x m' `star`
      pure (global_anchor_pred x m m'))


let elim_global_anchor (#o:_) (x:t) (m:repr)
  : STGhost (erased (PM.map tid aval)) o
       (global_anchor x m)
       (fun m' -> G.pts_to x m')
       (requires True)
       (ensures fun m' -> global_anchor_pred x m m')
  = let m' = elim_exists () in
    elim_pure _;
    m'

////////////////////////////////////////////////////////////////////////////////

let tids_pts_to_pred (x:t)
                     (frac:perm)
                     (m:repr)
                     (with_anchor:bool)
                     (m': PM.map tid aval)
  : prop
  = related_domains m m' /\
    (forall (tid:tid).{:pattern (Map.sel m tid) \/ (has_key m' tid)}
           (has_key m' tid ==>
             perm_ok m' tid /\
             perm_of m' tid == Some frac /\
             (with_anchor <==> has_anchor m' tid) /\
             get m' tid == Some?.v (Map.sel m tid)))

let tids_pts_to (x:t)
                ([@@@smt_fallback] frac:perm)
                ([@@@smt_fallback] m:repr)
                (with_anchor:bool)
  : vprop
  = exists_ (fun m' ->
    G.pts_to x m' `star`
    pure (tids_pts_to_pred x frac m with_anchor m'))

let intro_tids_pts_to (#o:_)
                      (x:t)
                      (frac:perm)
                      (m:repr)
                      (with_anchor:bool)
                      (m':PM.map tid aval)
  : STGhost unit o
       (G.pts_to x m')
       (fun _ -> tids_pts_to x frac m with_anchor)
       (requires tids_pts_to_pred x frac m with_anchor m')
       (ensures fun _ -> True)
  = intro_pure (tids_pts_to_pred x frac m with_anchor m');
    intro_exists m' (fun m' ->
      G.pts_to x m' `star`
      pure (tids_pts_to_pred x frac m with_anchor m'))

let elim_tids_pts_to (#o:_)
                     (x:t)
                     (frac:perm)
                     (m:repr)
                     (with_anchor:bool)
  : STGhost (erased (PM.map tid aval)) o
       (tids_pts_to x frac m with_anchor)
       (fun m' -> G.pts_to x m')
       (requires True)
       (ensures fun m' -> tids_pts_to_pred x frac m with_anchor m')
  = let m' = elim_exists () in
    elim_pure _;
    m'

////////////////////////////////////////////////////////////////////////////////
let singleton (t:tid) (l:log)
  : repr
  = Map.upd (Map.const None) t (Some l)

let tid_pts_to (x:t)
               (t:tid)
               ([@@@smt_fallback] frac:perm)
               ([@@@smt_fallback] l:log)
               (with_anchor:bool)
  : vprop
  = tids_pts_to x frac (singleton t l) with_anchor

////////////////////////////////////////////////////////////////////////////////

let snapshot_pred (x:t)
                  (m:repr)
                  (m':PM.map tid aval)
  : prop
  = related_domains m m' /\
    (forall tid. has_key m' tid ==>
            get m' tid == Some?.v (Map.sel m tid) /\
            no_ownership m' tid)

let global_snapshot (x:t)
                    ([@@@smt_fallback] m:repr)
  : vprop
  = exists_ (fun m' ->
      G.pts_to x m' `star`
      pure (snapshot_pred x m m'))


let intro_global_snapshot (#o:_)
                          (x:t)
                          (m:repr)
                          (m':PM.map tid aval)
  : STGhost unit o
    (G.pts_to x m')
    (fun _ -> global_snapshot x m)
    (requires snapshot_pred x m m')
    (ensures fun _ -> True)
  = intro_pure (snapshot_pred x m m');
    intro_exists m' (fun m' -> G.pts_to x m' `star` pure (snapshot_pred x m m'))


let elim_global_snapshot (#o:_)
                         (x:t)
                         (m:repr)
  : STGhost (PM.map tid aval) o
    (global_snapshot x m)
    (fun m' -> G.pts_to x m')
    (requires True)
    (ensures fun m' -> snapshot_pred x m m')
  = let m' = elim_exists () in
    elim_pure _;
    m'

////////////////////////////////////////////////////////////////////////////////
(*** Utilities ***)

let map_map (m:PM.map tid aval)
            (f:(tid:tid -> a:FAP.avalue anchors{ Map.sel m tid == FAP.Owns a } -> FAP.avalue anchors))
  : GTot (PM.map tid aval)
  = Map.map_literal (fun tid ->
       match Map.sel m tid with
       | FAP.Owns m -> FAP.Owns (f tid m)
       | FAP.Nothing -> FAP.Nothing)


let gpts_to_composable (#o:_) (x:t) (m0 m1:PM.map tid aval)
  : STGhost unit o
    (G.pts_to x m0 `star` G.pts_to x m1)
    (fun _ -> G.pts_to x m0 `star` G.pts_to x m1)
    (requires True)
    (ensures fun _ -> PM.composable_maps fap m0 m1)
 = let _ = G.gather x m0 m1 in
   G.share x _ m0 m1


let re_share (#o:_) (x:t) (m0 m1:PM.map tid aval)
                          (m0' m1':PM.map tid aval)
  : STGhost unit o
    (G.pts_to x m0 `star` G.pts_to x m1)
    (fun _ -> G.pts_to x m0' `star` G.pts_to x m1')
    (requires
      PM.composable_maps fap m0 m1 /\
      PM.composable_maps fap m0' m1' /\
      PM.compose_maps fap m0' m1' `Map.equal` PM.compose_maps fap m0 m1)
    (ensures fun _ -> True)
 = let _ = G.gather x m0 m1 in
   G.share x _ m0' m1'

(*** Operations ***)


////////////////////////////////////////////////////////////////////////////////
// Allocation
////////////////////////////////////////////////////////////////////////////////

let alloc0 (#o:_) (_:unit)
  : STGhostT t o
    emp
    (fun t -> G.pts_to t (Map.const (FAP.Owns (FAP.initial_value Seq.empty))))
  = G.alloc (Map.const (FAP.Owns (FAP.initial_value Seq.empty)))


#push-options "--query_stats --fuel 0 --ifuel 0"
let split_anchor1 (m:PM.map tid aval)
  : Lemma
    (requires
      forall (k:tid{has_key m k}).{:pattern (Map.sel m k)}
        anchors (get m k) (get m k) /\
        owns_key m k)
    (ensures
      PM.composable_maps fap
        (map_map m (fun _ a -> fst (FAP.anchored_snapshot a)))
        (map_map m (fun _ a -> snd (FAP.anchored_snapshot a))))
  = ()
#pop-options

let split_anchor2 (m:PM.map tid aval)
  : Lemma
    (requires
      (forall (k:tid{has_key m k}).{:pattern (Map.sel m k)}
        anchors (get m k) (get m k) /\
        owns_key m k ) /\
      PM.composable_maps fap
        (map_map m (fun _ a -> fst (FAP.anchored_snapshot a)))
        (map_map m (fun _ a -> snd (FAP.anchored_snapshot a))))
    (ensures
      m `Map.equal` PM.compose_maps fap
           (map_map m (fun _ a -> fst (FAP.anchored_snapshot a)))
           (map_map m (fun _ a -> snd (FAP.anchored_snapshot a)))
      )
  = let m1 = 
        PM.compose_maps fap
           (map_map m (fun _ a -> fst (FAP.anchored_snapshot a)))
           (map_map m (fun _ a -> snd (FAP.anchored_snapshot a)))
    in
    let _ = 
      introduce forall k. Map.sel m k == Map.sel m1 k
      with (
        ()
      )
    in
    Map.lemma_equal_intro m m1

let split_anchor (m:PM.map tid aval)
  : Lemma
    (requires
      forall (k:tid{has_key m k}).{:pattern (Map.sel m k)}
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
  = split_anchor1 m;
    split_anchor2 m


let alloc (#o:_) (_:unit)
  : STGhostT t o
             emp
             (fun t -> tids_pts_to t full_perm (Map.const (Some Seq.empty)) false `star`
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
    let mm0 : repr = Map.const (Some Seq.empty) in
    intro_tids_pts_to x full_perm mm0 false m0;
    intro_global_anchor x mm0 m1;
    //TODO: leave out these rewrites and the tactic crashes with a scoping error
    rewrite (tids_pts_to _ _ _ _)
            (tids_pts_to x full_perm (Map.const (Some Seq.empty)) false);
    rewrite (global_anchor _ _)
            (global_anchor x (Map.const (Some Seq.empty)));
    x

////////////////////////////////////////////////////////////////////////////////
// share_tids
////////////////////////////////////////////////////////////////////////////////
let split_perm (x:FAP.avalue anchors {
                      FAP.has_nonzero (FAP.avalue_perm x) /\
                      not (FAP.has_anchor (FAP.avalue_perm x)) /\
                      FAP.perm_ok x
               })
  : y:FAP.avalue anchors { FAP.avalue_composable y y }
  = let (Some p, None), v = x in
    (Some (half_perm p), None), v

#push-options "--query_stats --fuel 0"
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

let share_tids_pts_to_lemma (x:t)
                            (f:perm)
                            (m:repr) (m':PM.map tid aval)
  : Lemma
    (requires tids_pts_to_pred x f m false m')
    (ensures
      tids_pts_to_pred x (half_perm f) m false (map_map m' (fun _ -> split_perm)))
  = ()

let share_tids_pts_to (#o:_) (#f:perm) (x:t) (m:repr)
  : STGhostT unit o
    (tids_pts_to x f m false)
    (fun _ -> tids_pts_to x (half_perm f) m false `star` tids_pts_to x (half_perm f) m false)
  = let m' : erased (PM.map tid aval) = elim_exists () in
    elim_pure _;
    split_ownership f m';
    let half_m' = map_map m' (fun _ -> split_perm) in
    G.share x m' half_m' half_m';
    share_tids_pts_to_lemma x f m m';
    intro_tids_pts_to x (half_perm f) m _ half_m';
    intro_tids_pts_to x (half_perm f) m _ half_m'

////////////////////////////////////////////////////////////////////////////////
//take_tid
////////////////////////////////////////////////////////////////////////////////

let take_tid_lemma (x:t) (f:perm) (m:repr) (m':PM.map tid aval) (t:tid)
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
  =  ()


let take_tid (#o:_) (#f:perm) (x:t) (m:repr) (t:tid { Some? (Map.sel m t) })
  : STGhostT unit o
    (tids_pts_to x f m false)
    (fun _ -> tid_pts_to x t f (Some?.v (Map.sel m t)) false `star`
           tids_pts_to x f (Map.upd m t None) false)
  = let m' : erased (PM.map tid aval) = elim_exists() in
    elim_pure _;
    take_tid_lemma x f m m' t;
    let m0' = Map.upd m' t FAP.Nothing in
    let m1' = Map.upd (Map.const FAP.Nothing) t (Map.sel m' t) in
    G.share x m' m0' m1';
    intro_tids_pts_to x f (Map.upd m t None) false m0';
    let m1 : repr = singleton t (Some?.v (Map.sel m t)) in
    intro_tids_pts_to x f m1 false m1';
    rewrite (tids_pts_to x f m1 false)
            (tid_pts_to x t f (Some?.v (Map.sel m t)) false)

////////////////////////////////////////////////////////////////////////////////
//gather_tids
////////////////////////////////////////////////////////////////////////////////

let gather_tids_pts_to_lemma (x:t) (f0 f1:perm) (m:repr) (m0 m1:PM.map tid aval)
  : Lemma
    (requires
      tids_pts_to_pred x f0 m false m0 /\
      tids_pts_to_pred x f1 m false m1 /\
      PM.composable_maps fap m0 m1)
    (ensures tids_pts_to_pred x (sum_perm f0 f1) m false (PM.compose_maps fap m0 m1))
  = ()


let gather_tids_pts_to (#o:_) (#f0 #f1:perm) (x:t) (m:repr)
  : STGhostT unit o
    (tids_pts_to x f0 m false `star` tids_pts_to x f1 m false)
    (fun _ -> tids_pts_to x (sum_perm f0 f1) m false)
  = let m0 = elim_tids_pts_to x f0 m false in
    let m1 = elim_tids_pts_to x f1 m false in
    gpts_to_composable x m0 m1;
    gather_tids_pts_to_lemma x f0 f1 m m0 m1;
    G.gather x m0 m1;
    intro_tids_pts_to x (sum_perm f0 f1) m false _

////////////////////////////////////////////////////////////////////////////////
//gather_tid
////////////////////////////////////////////////////////////////////////////////
let gather_tid_pts_to (#o:_) (#tid:tid) (#f0 #f1:perm) (#l0 #l1:log) (x:t)
  : STGhost unit o
    (tid_pts_to x tid f0 l0 false `star` tid_pts_to x tid f1 l1 false)
    (fun _ -> tid_pts_to x tid (sum_perm f0 f1) l0 false)
    (requires True)
    (ensures fun _ -> l0 == l1)
  = let m0 = elim_tids_pts_to x f0 (singleton tid l0) false in
    let m1 = elim_tids_pts_to x f1 (singleton tid l1) false in
    gpts_to_composable x m0 m1;
    G.gather x m0 m1;
    intro_tids_pts_to x (sum_perm f0 f1) (singleton tid l0) false _

////////////////////////////////////////////////////////////////////////////////
//share_tid
////////////////////////////////////////////////////////////////////////////////
let share_tid_pts_to (#o:_) (#tid:tid) (#f:perm) (#l:log) (x:t)
  : STGhostT unit o
    (tid_pts_to x tid f l false)
    (fun _ -> tid_pts_to x tid (half_perm f) l false `star`
           tid_pts_to x tid (half_perm f) l false)
  = share_tids_pts_to x (singleton tid l)

////////////////////////////////////////////////////////////////////////////////
//update_tid_log
////////////////////////////////////////////////////////////////////////////////
let update_tid_log (#o:_) (x:t) (t:tid) (l0 l1:log)
  : STGhost unit o
    (tid_pts_to x t full_perm l0 false)
    (fun _ -> tid_pts_to x t full_perm l1 false)
    (requires
      l1 `compat_with_any_anchor_of` l0 /\
      l0 `log_grows` l1)
    (ensures fun _ -> True)
  = let m = elim_tids_pts_to x _ _ _ in
    G.upd_gen x m _ (update_anchored_value l1 m t);
    intro_tids_pts_to x full_perm (singleton t l1) false (put_anchored m t l1)

////////////////////////////////////////////////////////////////////////////////
//Extract anchor invariant
////////////////////////////////////////////////////////////////////////////////

let extract_anchor_invariant (#o:_)
                             (x:t)
                             (m:repr)
                             (t:tid)
                             (f:perm)
                             (l:log)
  : STGhost unit o
    (tid_pts_to x t f l false `star` global_anchor x m)
    (fun _ ->  tid_pts_to x t f l false `star` global_anchor x m)
    (requires
      Some? (Map.sel m t))
    (ensures fun _ ->
      Some? (Map.sel m t) /\
      M.committed_log_entries l == Some?.v (Map.sel m t))
  = let m0 = elim_tids_pts_to x _ _ _ in
    let m1 = elim_global_anchor x _ in
    gpts_to_composable x m0 m1;
    intro_tids_pts_to x f _ false m0;
    intro_global_anchor x m m1

////////////////////////////////////////////////////////////////////////////////
//take_anchor_tid
////////////////////////////////////////////////////////////////////////////////
let take_anchor_tid_lemma (x:t)
                          (m0 m1:PM.map tid aval)
                          (m:repr)
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
      PM.compose_maps fap m0' m1' `Map.equal`
      PM.compose_maps fap m0 m1 /\
      M.committed_log_entries l == Some?.v (Map.sel m t))))
  = ()


let take_anchor_tid (#o:_) (x:t) (m:repr)
                           (t:tid) (f:perm) (l:log)
  : STGhost unit o
    (tid_pts_to x t f l false `star` global_anchor x m)
    (fun _ -> tid_pts_to x t f l true `star`
           global_anchor x (Map.upd m t None))
    (requires
      Some? (Map.sel m t))
    (ensures fun _ ->
      Some? (Map.sel m t) /\
      M.committed_log_entries l == Some?.v (Map.sel m t))
  = let m0 = elim_tids_pts_to x f _ _ in
    let m1 = elim_global_anchor x m in
    gpts_to_composable x m0 m1;
    take_anchor_tid_lemma x m0 m1 m t f l;
    let FAP.Owns ((_, Some anchor), _) = Map.sel m1 t in
    let FAP.Owns (_, v) = Map.sel m0 t in
    let av' = (Some f, Some anchor), v in
    let m0' = Map.upd m0 t (FAP.Owns av') in
    let m1' = Map.upd m1 t FAP.Nothing in
    re_share x m0 m1 m0' m1';
    intro_tids_pts_to x f (singleton t l) true m0';
    intro_global_anchor x (Map.upd m t None) m1'

////////////////////////////////////////////////////////////////////////////////
//update_anchored_tid_log
////////////////////////////////////////////////////////////////////////////////
let update_anchored_tid_log (#o:_) (x:t) (t:tid) (l0 l1:log)
  : STGhost unit o
    (tid_pts_to x t full_perm l0 true)
    (fun _ -> tid_pts_to x t full_perm l1 true)
    (requires
      l0 `log_grows` l1 /\
      M.committed_log_entries l1 == l1)
    (ensures fun _ -> True)
  = let m = elim_tids_pts_to x _ _ _ in
    G.upd_gen x m _ (update_value l1 m t);
    intro_tids_pts_to x full_perm (singleton t l1) true (put m t l1)

////////////////////////////////////////////////////////////////////////////////
//put_anchor_tid
////////////////////////////////////////////////////////////////////////////////
let put_anchor_tid_lemma (x:t)
                         (m0 m1:PM.map tid aval)
                         (m:repr)
                         (t:tid)
                         (f:perm)
                         (l:log)
  : Lemma
    (requires
      tids_pts_to_pred x f (singleton t l) true m0 /\
      global_anchor_pred x m m1 /\
      PM.composable_maps fap m0 m1 /\
      l == M.committed_log_entries l)
    (ensures (
      None? (Map.sel m t) /\
      has_key m0 t /\ (
      let FAP.Owns av = Map.sel m0 t in
      let av0, av1 = FAP.anchored_snapshot av in
      let m0' = Map.upd m0 t (FAP.Owns av0) in
      let m1' = Map.upd m1 t (FAP.Owns av1) in
      tids_pts_to_pred x f (singleton t l) false m0' /\
      global_anchor_pred x (Map.upd m t (Some l)) m1' /\
      PM.composable_maps fap m0' m1' /\
      PM.compose_maps fap m0' m1' `Map.equal`
      PM.compose_maps fap m0 m1)))
  = ()

let put_anchor_tid (#o:_) (x:t) (m:repr)
                          (t:tid) (f:perm) (l:log)
  : STGhost unit o
    (tid_pts_to x t f l true `star` global_anchor x m)
    (fun _ -> tid_pts_to x t f l false `star`
           global_anchor x (Map.upd m t (Some l)))
    (requires
      M.committed_log_entries l == l)
    (ensures fun _ -> True)
  = let m0 = elim_tids_pts_to x f _ _ in
    let m1 = elim_global_anchor x m in
    gpts_to_composable x m0 m1;
    put_anchor_tid_lemma x m0 m1 m t f l;
    let FAP.Owns av = Map.sel m0 t in
    let av0, av1 = FAP.anchored_snapshot av in
    let m0' = Map.upd m0 t (FAP.Owns av0) in
    let m1' = Map.upd m1 t (FAP.Owns av1) in
    re_share x m0 m1 m0' m1';
    intro_tids_pts_to x f (singleton t l) false m0';
    intro_global_anchor x (Map.upd m t (Some l)) m1'

////////////////////////////////////////////////////////////////////////////////
//take_snapshot
////////////////////////////////////////////////////////////////////////////////
#push-options "--z3rlimit_factor 2"
let take_snapshot (#o:_) (x:t) (m:repr)
  : STGhostT unit o
    (global_anchor x m)
    (fun _ -> global_anchor x m `star` global_snapshot x m)
  = let m' = elim_global_anchor x m in
    let m'' = map_map m' (fun _ a -> (None, None), snd a) in
    assert (Map.equal m' (PM.compose_maps fap m' m''));
    G.share x m' m' m'';
    intro_global_snapshot x m m'';
    intro_global_anchor x m m'
#pop-options

////////////////////////////////////////////////////////////////////////////////
// dup_snapshot
////////////////////////////////////////////////////////////////////////////////
let dup_snapshot (#o:_) (x:t) (m:repr)
  : STGhostT unit o
    (global_snapshot x m)
    (fun _ -> global_snapshot x m `star` global_snapshot x m)
  = let m' = elim_global_snapshot x m in
    assert (Map.equal m' (PM.compose_maps fap m' m'));
    G.share x m' m' m';
    intro_global_snapshot x m m';
    intro_global_snapshot x m m'

////////////////////////////////////////////////////////////////////////////////
// recall_snapshot
////////////////////////////////////////////////////////////////////////////////
let recall_snapshot (#o:_) (x:t) (m:repr) (f:perm) (t:tid) (l:log) (with_anchor:bool)
  : STGhost unit o
    (global_snapshot x m `star` tid_pts_to x t f l with_anchor)
    (fun _ -> global_snapshot x m `star` tid_pts_to x t f l with_anchor)
    (requires True)
    (ensures fun _ ->
      Some? (Map.sel m t) ==>
      Some?.v (Map.sel m t) `log_grows` l)
  = let m' = elim_global_snapshot x m in
    let m'' = elim_tids_pts_to x f _ _ in
    gpts_to_composable x m' m'';
    intro_global_snapshot x m m';
    intro_tids_pts_to x f (singleton t l) with_anchor m''

////////////////////////////////////////////////////////////////////////////////
//global_anchor_committed
////////////////////////////////////////////////////////////////////////////////
let global_anchor_committed (#o:_) (#m:repr) (x:t)
  : STGhost unit o
    (global_anchor x m)
    (fun _ -> global_anchor x m)
    (requires True)
    (ensures fun _ ->
      forall tid. match Map.sel m tid with
             | None -> True
             | Some l -> M.committed_log_entries l == l)
  = let m' = elim_global_anchor x m in
    intro_global_anchor x m m'
