module Zeta.Steel.FractionalAnchoredPreorder
open Steel.ST.Util
open FStar.Map
open FStar.PCM
open FStar.Preorder
open Steel.Preorder
open Zeta.Steel.Util
open FStar.TSet
open Steel.FractionalPermission
#push-options "--z3cliopt 'smt.qi.eager_threshold=100' --fuel 0 --ifuel 2 --z3rlimit_factor 4"
let permission (v:Type) =
  (option perm  //a fractional permission; indicates some ownership, with Some full allowing writes compatible with the last commit
   & option v)  //an optional anchor

let has_advanceable #v (p:permission v) = Some? (fst p)
let has_anchor #v (p:permission v) = Some? (snd p)
let has_some_ownership #v (p:permission v) = has_advanceable p || has_anchor p
let anchor_of #v (p:permission v { has_anchor p }) : v = Some?.v (snd p)

// a reflexive relation controls how far an element can be updated
let anchor_rel (#v:Type) (p:preorder v) =
  anchors:(v -> v -> prop) {
    (forall v0 v1. anchors v0 v1 ==> p v0 v1) /\
    (forall v. v `anchors` v) /\
    (forall x z. x `anchors` z  ==> (forall y. p x y /\ p y z ==> x `anchors` y)) //if x `anchors` z then it also anchors any `y` between x and z
  }

let anchored (#v:Type) (#p:preorder v) (anchors:anchor_rel p)
             (pv:(permission v & vhist p))
  = has_anchor (fst pv) ==> anchor_of (fst pv) `anchors` curval (snd pv)

let avalue (#v:Type) (#p:preorder v) (anchors:anchor_rel p)
  = pv:(permission v & vhist p) { anchored anchors pv }

#push-options "--fuel 1"
let initial_value (#v:Type) (#p:preorder v) (#anchors:anchor_rel p) (value:v)
  : avalue anchors
  = (Some full, Some value), [value]
#pop-options

[@@erasable]
noeq
type knowledge (#v:Type) (#p:preorder v) (anchors:anchor_rel p) =
  | Owns     : avalue anchors -> knowledge anchors
  | Nothing  : knowledge anchors

let b2p (b:bool)
  : prop
  = b == true

let perm_opt_composable (p0 p1:option perm)
  : prop
  = match p0, p1 with
    | None, None -> True
    | Some p, None
    | None, Some p -> b2p (p `lesser_equal_perm` full)
    | Some p0, Some p1 -> b2p (sum_perm p0 p1 `lesser_equal_perm` full)

let compose_perm_opt (p0 p1:option perm) =
  match p0, p1 with
  | None, p
  | p, None -> p
  | Some p0, Some p1 -> Some (sum_perm p0 p1)

let permission_composable #v (p0 p1 : permission v)
  : prop
  = let q0, s0 = p0 in
    let q1, s1 = p1 in
    perm_opt_composable q0 q1 /\  // some of fracs can't exceed 1
    not (Some? s0 && Some? s1)   // at most one can have an anchor

let compose_permissions (#v:_) (p0:permission v) (p1:permission v{permission_composable p0 p1})
  : permission v
  = compose_perm_opt (fst p0) (fst p1),
    (match snd p0, snd p1 with
     | None, a
     | a, None -> a)

let avalue_composable (#v:Type) (#p:preorder v) (#anchors:anchor_rel p)
                      (av0 av1: avalue anchors)
   : prop
   = let (p0, v0) = av0 in
     let (p1, v1) = av1 in
     permission_composable p0 p1 /\
    (if not (has_some_ownership p0)
     && not (has_some_ownership p1)
     then p_composable _ v0 v1 //neither has ownership, one history is older than the other
     else if not (has_some_ownership p0)
          && has_some_ownership p1
     then (
          if has_advanceable p1
          then v1 `extends` v0 //the one with ownership is more recent
          else (p_composable _ v0 v1 /\
               (v0 `extends` v1 ==> anchor_of p1 `anchors` curval v0))
     )
     else if has_some_ownership p0
          && not (has_some_ownership p1)
     then (
          if has_advanceable p0
          then v0 `extends` v1
          else (p_composable _ v0 v1 /\
                (v1 `extends` v0 ==> anchor_of p0 `anchors` curval v1))
     )
     else (
       assert (has_some_ownership p0 && has_some_ownership p1);
       if has_anchor p0 && has_anchor p1 //at most one can sync
       then False
       else if has_advanceable p0 && has_advanceable p1
       then v0 == v1 //if both are advanceable, then they must both only have read permission and must agree on the value
       else if has_advanceable p0 && has_anchor p1
       then ( assert (not (has_advanceable p1));
              v0 `extends` v1 /\           //v0 has advanceable ownership, so extends
              anchor_of p1 `anchors` curval v0  //but not beyond what is allowed by s
            )
       else if has_anchor p0 && has_advanceable p1 //symmetric
       then ( assert (not (has_advanceable p0));
              v1 `extends` v0 /\
              anchor_of p0 `anchors` curval v1  //v1 extends, but not beyond what is allowed by s
            )
       else (assert false; False))) //exhaustive

let composable #v (#p:preorder v) (#a:anchor_rel p)
  : symrel (knowledge a)
  = fun (k0 k1:knowledge a) ->
    match k0, k1 with
    | Nothing, _
    | _, Nothing -> True

    | Owns m, Owns m' ->
      avalue_composable m m'

let p_op (#a: Type u#a) (q:preorder a) (x:vhist q) (y:vhist q{p_composable q x y}) : vhist q =
  p_op _ x y

let compose_avalue (#v:Type) (#p:preorder v) (#anchors:anchor_rel p)
                   (m0:avalue anchors)
                   (m1:avalue anchors { avalue_composable m0 m1 } )
  : avalue anchors
  =  let p0, v0 = m0 in
     let p1, v1 = m1 in
     let p12 = compose_permissions p0 p1 in
     let v12 = p_op _ v0 v1 in
     p12, v12

let compose_avalue_comm (#v:Type) (#p:preorder v) (#anc:anchor_rel p)
                        (m0: avalue anc)
                        (m1: avalue anc{ avalue_composable m0 m1 })
 : Lemma (compose_avalue m0 m1 == compose_avalue m1 m0)
 = ()

let avalue_composable_assoc_l (#v:Type) (#p:preorder v) (#anchors:anchor_rel p)
                              (m0: avalue anchors)
                              (m1: avalue anchors)
                              (m2: avalue anchors {
                                avalue_composable m1 m2 /\
                                avalue_composable m0 (compose_avalue m1 m2)
                              })
 : Lemma (avalue_composable m0 m1 /\
          avalue_composable (compose_avalue m0 m1) m2)
 = ()

let compose_avalue_assoc_l (#v:Type) (#p:preorder v) (#s:anchor_rel p)
                           (m0: avalue s)
                           (m1: avalue s)
                           (m2: avalue s {
                             avalue_composable m1 m2 /\
                             avalue_composable m0 (compose_avalue m1 m2)
                           })
 : Lemma (avalue_composable m0 m1 /\
          avalue_composable (compose_avalue m0 m1) m2 /\
          compose_avalue m0 (compose_avalue m1 m2) ==
          compose_avalue (compose_avalue m0 m1) m2)
 = avalue_composable_assoc_l m0 m1 m2

let avalue_composable_assoc_r (#v:Type) (#p:preorder v) (#anchors:anchor_rel p)
                            (m0: avalue anchors)
                            (m1: avalue anchors)
                            (m2: avalue anchors {
                              avalue_composable m0 m1 /\
                              avalue_composable (compose_avalue m0 m1) m2
                            })
 : Lemma (avalue_composable m1 m2 /\
          avalue_composable m0 (compose_avalue m1 m2))
 = ()


let compose_avalue_assoc_r (#v:Type) (#p:preorder v) (#s:anchor_rel p)
                           (m0: avalue s)
                           (m1: avalue s)
                           (m2: avalue s{
                             avalue_composable m0 m1 /\
                             avalue_composable (compose_avalue m0 m1) m2
                           })
 : Lemma (avalue_composable m1 m2 /\
          avalue_composable m0 (compose_avalue m1 m2) /\
          compose_avalue m0 (compose_avalue m1 m2) ==
          compose_avalue (compose_avalue m0 m1) m2)
 = avalue_composable_assoc_r m0 m1 m2

let compose (#v:Type) (#p:preorder v) (#s:anchor_rel p)
            (k0:knowledge s)
            (k1:knowledge s{ composable k0 k1 })
  : knowledge s
  = match k0, k1 with
    | Nothing, k
    | k, Nothing -> k

    | Owns m, Owns m' ->
      Owns (compose_avalue m m')

let composable_assoc_r #v (#p:preorder v) (#s:anchor_rel p)
                       (k0 k1 k2: knowledge s)
  : Lemma
    (requires  composable k0 k1 /\
               composable (compose k0 k1) k2)
    (ensures
               composable k1 k2 /\
               composable k0 (compose k1 k2) /\
               compose k0 (compose k1 k2) ==
               compose (compose k0 k1) k2
               )
  = match k0, k1, k2 with
    | Nothing, _, _
    | _, Nothing, _
    | _, _, Nothing -> ()
    | Owns m0, Owns m1, Owns m2 ->
      compose_avalue_assoc_r m0 m1 m2

let composable_assoc_l #v (#p:preorder v) (#s:anchor_rel p)
                          (k0 k1 k2: knowledge s)
  : Lemma
    (requires
               composable k1 k2 /\
               composable k0 (compose k1 k2))
    (ensures   composable k0 k1 /\
               composable (compose k0 k1) k2 /\
               compose k0 (compose k1 k2) ==
               compose (compose k0 k1) k2)
  = match k0, k1, k2 with
    | Nothing, _, _
    | _, Nothing, _
    | _, _, Nothing -> ()
    | Owns m0, Owns m1, Owns m2 ->
      compose_avalue_assoc_l m0 m1 m2


let p0 #v #p #s : pcm' (knowledge #v #p s) = {
  composable;
  op=compose;
  one=Nothing
}

let avalue_perm (#v:Type)
                (#p:preorder v)
                (#s:anchor_rel p)
                (m:avalue s)
    = fst m

let avalue_owns (#v:Type)
                (#p:preorder v)
                (#s:anchor_rel p)
                (m:avalue s)
  : prop
  = fst (avalue_perm m) == Some full /\
    Some? (snd (avalue_perm m))

let full_knowledge #v #p #s (kn:knowledge #v #p s)
  : prop
  = match kn with
    | Nothing -> False
    | Owns km -> avalue_owns km

let pcm #v #p #s : pcm (knowledge #v #p s) = {
  p = p0;
  comm = (fun k0 k1 ->
             match k0, k1 with
             | Nothing, _
             | _, Nothing -> ()
             | Owns m0, Owns m1 ->
               compose_avalue_comm m0 m1);
  assoc = (fun k0 k1 k2 -> composable_assoc_l k0 k1 k2);
  assoc_r = (fun k0 k1 k2 -> composable_assoc_r k0 k1 k2);
  is_unit = (fun _ -> ());
  refine = full_knowledge;
}

let avalue_val (#v:Type)
               (#p:preorder v)
               (#s:anchor_rel p)
               (m:avalue #v #p s)
    = snd m

let avalue_update (#v:Type)
                  (#p:preorder v)
                  (#s:anchor_rel p)
                  (m:avalue s)
                  (value:vhist p)
  : avalue s
  = let p, _ = avalue_perm m in
    let p' = p, Some (curval value) in
    (p', value)

#push-options "--query_stats"
let update_hist (#v:Type)
                (#p:preorder v)
                (#s:anchor_rel p)
                (m:avalue s)
                (v1:vhist p {
                      avalue_owns m /\
                      v1 `extends` avalue_val m
                })
  : frame_preserving_upd pcm (Owns m) (Owns (avalue_update m v1))
  = fun full_v ->
      let Owns full_m = full_v in
      let m_res = avalue_update full_m v1 in
      Owns m_res

let avalue_update_value (#v:Type)
                        (#p:preorder v)
                        (#s:anchor_rel p)
                        (m:avalue s)
                        (value:v { curval (avalue_val m) `p` value })
  : m':avalue s {
       curval (avalue_val m') == value /\
       avalue_val m'  `extends` avalue_val m
    }
  = let v = avalue_val m in
    avalue_update m (extend_history v value)

let update_value (#v:Type)
                 (#p:preorder v)
                 (#s:anchor_rel p)
                 (m:avalue s)
                 (v1:v {
                   avalue_owns m /\ //if you have full ownership of key
                   curval (avalue_val m) `p` v1 //you can update it wrt the preorder only
                 })
  : frame_preserving_upd pcm (Owns m) (Owns (avalue_update_value m v1))
  = coerce_eq () (update_hist m (extend_history (avalue_val m) v1)) //F* goes nuts and starts swallowing gobs of memory without the coerce_eq: TODO, debug

let avalue_owns_anchored (#v:Type)
                         (#p:preorder v)
                         (#s:anchor_rel p)
                         (m:avalue s)
    = fst (avalue_perm m) == Some full /\
      None? (snd (avalue_perm m))

let compat_with_any_anchor_of (#v:Type)
                           (#p:preorder v)
                           (#anchors:anchor_rel p)
                           (v1:v)
                           (v0:avalue anchors)
  = forall (anchor:v). anchor `anchors` curval (avalue_val v0) ==>
                  anchor `anchors` v1

let avalue_anchored_update (#v:Type)
                           (#p:preorder v)
                           (#s:anchor_rel p)
                           (m:avalue s)
                           (value:vhist p {
                                curval value `compat_with_any_anchor_of` m
                           })
  : avalue s
  = avalue_perm m, value

let update_anchored_hist (#v:Type)
                         (#p:preorder v)
                         (#s:anchor_rel p)
                         (m:avalue s)
                         (v1:vhist p {
                           avalue_owns_anchored m /\
                           v1 `extends` avalue_val m /\
                           curval v1 `compat_with_any_anchor_of` m
                         })
  : frame_preserving_upd pcm (Owns m) (Owns (avalue_anchored_update m v1))
  = fun full_v ->
      let Owns full_m = full_v in
      let m_res = avalue_anchored_update full_m v1 in
      Owns m_res

let avalue_update_anchored_value (#v:Type)
                                 (#p:preorder v)
                                 (#s:anchor_rel p)
                                 (m:avalue s)
                                 (value:v { curval (avalue_val m) `p` value /\
                                            value `compat_with_any_anchor_of` m })
  : m':avalue s {
       curval (avalue_val m') == value /\
       avalue_val m'  `extends` avalue_val m
    }
  = let v = avalue_val m in
    avalue_anchored_update m (extend_history v value)

let update_anchored_value (#v:Type)
                          (#p:preorder v)
                          (#s:anchor_rel p)
                          (m:avalue s)
                          (v1:v {
                            avalue_owns_anchored m /\ //if you own an anchored key, you can update if you respect
                            curval (avalue_val m) `p` v1 /\ //the preorder
                            v1 `compat_with_any_anchor_of` m //and respect any anchor of the current value
                          })
  : frame_preserving_upd pcm (Owns m) (Owns (avalue_update_anchored_value m v1))
  = coerce_eq () (update_anchored_hist m (extend_history (avalue_val m) v1))


let snapshot (#v:Type0) (#p:preorder v) (#s:anchor_rel p)
             (a: avalue s)
  : avalue s
  = (None, None), avalue_val a

let perm_ok #v #p #s (a:avalue #v #p s)
  = perm_opt_composable (fst (avalue_perm a)) None

let snapshot_lemma (#v:Type)
                   (#p:preorder v)
                   (#s:anchor_rel p)
                   (a:avalue s)
  : Lemma (requires perm_ok a)
          (ensures Owns a `composable` Owns (snapshot a))
  = ()

let snapshot_dup_lemma (#v:Type)
                       (#p:preorder v)
                       (#s:anchor_rel p)
                       (a:avalue s)
  : Lemma (requires perm_ok a)
          (ensures Owns (snapshot a) `composable` Owns (snapshot a))
  = ()

let anchored_snapshot (#v:Type0) (#p:preorder v) (#s:anchor_rel p)
                      (a: avalue s)
  : avalue s & avalue s
  = let (p,a0), v = a in
    let a =
      match a0 with
      | None -> Some (curval v)
      | Some a -> Some a
    in
    ((p, None), v),
    ((None, a), v)

let anchored_snapshot_lemma (#v:Type)
                            (#p:preorder v)
                            (#s:anchor_rel p)
                            (a:avalue s)
  : Lemma (requires avalue_owns a)
          (ensures (
            let owned, anchor = anchored_snapshot a in
            (Owns owned `composable` Owns anchor) /\
            compose_avalue owned anchor == a))
  = ()

// // ////////////////////////////////////////////////////////////////////////////////

// // let tmap (k:eqtype) (v:Type0) (c:preorder v) = Map.t k (hist c)

// // val t (k:eqtype) (v:Type0) (c:preorder v) : Type0

// // val k_of (#k:eqtype) (#v:Type0) (#c:preorder v)
// //          (t:t k v c)
// //          (knowledge: knowledge k v c)
// //   : vprop

// // val share  (#o:_)
// //            (#k:eqtype) (#v:Type0) (#c:preorder v)
// //            (#m0 :kmap k v c)
// //            (#m1: kmap k v c { kmap_composable m0 m1 })
// //            (t:t k v c)
// //   : STGhostT unit o
// //     (k_of t (Owns (compose_kmaps m0 m1)))
// //     (fun _ -> k_of t (Owns m0) `star` k_of t (Owns m1))

// // val gather (#o:_)
// //            (#k:eqtype) (#v:Type0) (#c:preorder v)
// //            (#m0 #m1: kmap k v c)
// //            (t:t k v c)
// //   : STGhostT (_:unit { kmap_composable m0 m1 }) o
// //     (k_of t (Owns m0) `star` k_of t (Owns m1))
// //     (fun _ -> k_of t (Owns (compose_kmaps m0 m1)))

// // let snapshot (#k:eqtype) (#v:Type0) (#c:preorder v)
// //              (m: kmap k v c)
// //   : Map.t k v
// //   = map_literal (fun k -> curval (snd (Map.sel m k)))

// // val global_snapshot (#k:eqtype) (#v:Type0) (#c:preorder v)
// //                     (t:t k v c)
// //                     ([@@@smt_fallback] m: Map.t k v)
// //   : vprop
// //   // = exists_ (fun (km:kmap k v c) ->
// //   //       pure (snapshot km == m) `star`
// //   //       k_of t (Owns (ksnapshot km)))

// // val take_snapshot (#o:_)
// //                   (#k:eqtype) (#v:Type0) (#c:preorder v)
// //                   (#m: kmap k v c)
// //                   (t:t k v c)
// //   : STGhostT unit o
// //     (k_of t (Owns m))
// //     (fun _ -> k_of t (Owns m) `star` global_snapshot t (snapshot m))

// // val owns_key (#k:eqtype) (#v:Type0) (#c:preorder v)
// //              (t:t k v c)
// //              (key:k)
// //              ([@@@smt_fallback]perm:perm)
// //              ([@@@smt_fallback]value:v)
// //  : vprop
// //   // = exists_ (fun (m:kmap k v c) ->
// //   //      pure ((forall key'. (key<>key' ==> fst (Map.sel m key') == None)) /\
// //   //            (match Map.sel m key with
// //   //             | None, _ -> False
// //   //             | Some p, h ->
// //   //               perm == p /\
// //   //               curval h == value)) `star`
// //   //      k_of t (Owns m))

// // val snapshot_of_key (#k:eqtype) (#v:Type0) (#c:preorder v)
// //                     (t:t k v c)
// //                     (key:k)
// //                     ([@@@smt_fallback]value:v)
// //  : vprop
// //   // = exists_ (fun (m:kmap k v c) ->
// //   //      pure ((forall key'. fst (Map.sel m key') == None) /\
// //   //            (match Map.sel m key with
// //   //             | Some _, _ -> False
// //   //             | None, h -> curval h == value)) `star`
// //   //      k_of t (Owns m))

// // val local_snapshot (#o:_)
// //                    (#k:eqtype) (#v:Type0) (#c:preorder v)
// //                    (#key:k) (#frac:_) (#value:v)
// //                    (t:t k v c)
// //   : STGhostT unit o
// //     (owns_key t key frac value)
// //     (fun _ -> owns_key t key frac value `star` snapshot_of_key t key value)

// // val dup_snapshot (#o:_)
// //                  (#k:eqtype) (#v:Type0) (#c:preorder v)
// //                  (#key:k) (#value:v)
// //                  (t:t k v c)
// //   : STGhostT unit o
// //     (snapshot_of_key t key value)
// //     (fun _ -> snapshot_of_key t key value `star` snapshot_of_key t key value)

// // val update (#o:_)
// //            (#k:eqtype) (#v:Type0) (#c:preorder v)
// //            (#key:k) (#value:v)
// //            (t:t k v c)
// //            (value':v {c value value'})
// //   : STGhostT unit o
// //     (owns_key t key full_perm value)
// //     (fun _ -> owns_key t key full_perm value')

// // val update_global_snapshot (#o:_)
// //                            (#k:eqtype) (#v:Type0) (#c:preorder v)
// //                            (#key:k) (#frac:_) (#value:v)
// //                            (t:t k v c)
// //                            (m:Map.t k v)
// //   : STGhostT unit o
// //     (owns_key t key frac value `star` global_snapshot t m)
// //     (fun _ -> owns_key t key frac value `star` global_snapshot t (Map.upd m key value))


// // val dup_global_snapshot (#o:_) (#k:eqtype) (#v:Type0) (#c:preorder v) (#m: Map.t k v)
// //                         (t:t k v c)
// //   : STGhostT unit o
// //     (global_snapshot t m)
// //     (fun _ -> global_snapshot t m `star` global_snapshot t m)
