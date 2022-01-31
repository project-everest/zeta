module Zeta.Steel.GhostSharedMap
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

let kmap_value (#v:Type) (p:preorder v) (anchors:anchor_rel p)
  = pv:(permission v & vhist p) { anchored anchors pv }

let kmap (k:eqtype) (v:Type) (p:preorder v) (anchors:anchor_rel p) =
  Map.t k (kmap_value p anchors)

#push-options "--fuel 1"
let initial_map (#k:eqtype) (#v:Type) (#p:preorder v) (#anchors:anchor_rel p)
                (f:option perm) (value:v)
  : kmap k v p anchors
  = map_literal (fun _ -> (((Some full, Some value) <: permission v), ([value] <: vhist p)) <:kmap_value p anchors)
#pop-options

[@@erasable]
noeq
type knowledge (k:eqtype) (v:Type) (p:preorder v) (anchors:anchor_rel p) =
  | Owns     : kmap k v p anchors -> knowledge k v p anchors
  | Nothing  : knowledge k v p anchors

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

let kmap_composable_k (#k:eqtype) (#v:Type) (#p:preorder v) (#anchors:anchor_rel p)
                      (m0 m1: kmap k v p anchors)
                      (key:k)
   : prop
   = let (p0, v0) = Map.sel m0 key in
     let (p1, v1) = Map.sel m1 key in
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

let kmap_composable (#k:eqtype) (#v:Type) (#p:preorder v) (#anchors:anchor_rel p) (m0 m1: kmap k v p anchors)
   : prop
   = forall k. kmap_composable_k m0 m1 k

let composable #k #v #p #a
  : symrel (knowledge k v p a)
  = fun (k0 k1:knowledge k v p a) ->
    match k0, k1 with
    | Nothing, _
    | _, Nothing -> True

    | Owns m, Owns m' ->
      kmap_composable m m'

let p_op (#a: Type u#a) (q:preorder a) (x:vhist q) (y:vhist q{p_composable q x y}) : vhist q =
  p_op _ x y

let compose_at_k (#k:eqtype) (#v:Type) (#p:preorder v) (#anchors:anchor_rel p)
                 (m0: kmap k v p anchors)
                 (m1: kmap k v p anchors)
                 (key:k { kmap_composable_k m0 m1 key})
  : kmap_value p anchors
  =  let p0, v0 = Map.sel m0 key in
     let p1, v1 = Map.sel m1 key in
     let p12 = compose_permissions p0 p1 in
     let v12 = p_op _ v0 v1 in
     p12, v12

let compose_kmaps (#k:eqtype) (#v:Type) (#p:preorder v) (#anc:anchor_rel p)
                  (m0: kmap k v p anc)
                  (m1: kmap k v p anc{ kmap_composable m0 m1 })
  : kmap k v p anc
  =  map_literal (compose_at_k m0 m1)

let compose_kmaps_comm (#k:eqtype) (#v:Type) (#p:preorder v) (#anc:anchor_rel p)
                       (m0: kmap k v p anc)
                       (m1: kmap k v p anc{ kmap_composable m0 m1 })
 : Lemma (compose_kmaps m0 m1 `Map.equal` compose_kmaps m1 m0)
         [SMTPat (compose_kmaps m0 m1);
          SMTPat (compose_kmaps m1 m0)]
 = ()

let kmap_composable_assoc (#k:eqtype) (#v:Type) (#p:preorder v) (#anchors:anchor_rel p)
                          (m0: kmap k v p anchors)
                          (m1: kmap k v p anchors)
                          (m2: kmap k v p anchors {
                            kmap_composable m1 m2 /\
                            kmap_composable m0 (compose_kmaps m1 m2)
                          })
 : Lemma (kmap_composable m0 m1 /\
          kmap_composable (compose_kmaps m0 m1) m2)
 = ()

let compose_maps_assoc (#k:eqtype) (#v:Type) (#p:preorder v) (#s:anchor_rel p)
                       (m0: kmap k v p s)
                       (m1: kmap k v p s)
                       (m2: kmap k v p s {
                         kmap_composable m1 m2 /\
                         kmap_composable m0 (compose_kmaps m1 m2)
                       })
 : Lemma (kmap_composable m0 m1 /\
          kmap_composable (compose_kmaps m0 m1) m2 /\
          compose_kmaps m0 (compose_kmaps m1 m2) `Map.equal`
          compose_kmaps (compose_kmaps m0 m1) m2)
         [SMTPat (compose_kmaps (compose_kmaps m0 m1) m2);
          SMTPat (compose_kmaps m0 (compose_kmaps m2 m2))]
 = kmap_composable_assoc m0 m1 m2


let kmap_composable_assoc_r (#k:eqtype) (#v:Type) (#p:preorder v) (#anchors:anchor_rel p)
                            (m0: kmap k v p anchors)
                            (m1: kmap k v p anchors)
                            (m2: kmap k v p anchors {
                              kmap_composable m0 m1 /\
                              kmap_composable (compose_kmaps m0 m1) m2
                            })
 : Lemma (kmap_composable m1 m2 /\
          kmap_composable m0 (compose_kmaps m1 m2))
 = ()


let compose_maps_assoc_r (#k:eqtype) (#v:Type) (#p:preorder v) (#s:anchor_rel p)
                       (m0: kmap k v p s)
                       (m1: kmap k v p s)
                       (m2: kmap k v p s{
                         kmap_composable m0 m1 /\
                         kmap_composable (compose_kmaps m0 m1) m2
                       })
 : Lemma (kmap_composable m1 m2 /\
          kmap_composable m0 (compose_kmaps m1 m2) /\
          compose_kmaps m0 (compose_kmaps m1 m2) `Map.equal`
          compose_kmaps (compose_kmaps m0 m1) m2)
         [SMTPat (compose_kmaps (compose_kmaps m0 m1) m2);
          SMTPat (compose_kmaps m0 (compose_kmaps m2 m2))]
 = kmap_composable_assoc_r m0 m1 m2

let compose #k #v #p #s (k0:knowledge k v p s)
                        (k1:knowledge k v p s{ composable k0 k1 })
  : knowledge k v p s
  = match k0, k1 with
    | Nothing, k
    | k, Nothing -> k

    | Owns m, Owns m' ->
      Owns (compose_kmaps m m')

let composable_assoc_r #k #v #p #s (k0 k1 k2: knowledge k v p s)
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
      compose_maps_assoc_r m0 m1 m2

let composable_assoc_l #k #v #p #s (k0 k1 k2: knowledge k v p s)
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
      compose_maps_assoc m0 m1 m2


let p0 #k #v #p #s : pcm' (knowledge k v p s) = {
  composable;
  op=compose;
  one=Nothing
}

let kmap_perm_of (#k:eqtype)
                 (#v:Type)
                 (#p:preorder v)
                 (#s:anchor_rel p)
                 (m:kmap k v p s)
                 (key:k)
    = fst (Map.sel m key)

let kmap_owns_key (#k:eqtype)
                  (#v:Type)
                  (#p:preorder v)
                  (#s:anchor_rel p)
                  (m:kmap k v p s)
                  (key:k)
    = fst (kmap_perm_of m key) == Some full /\
      Some? (snd (kmap_perm_of m key))

let full_knowledge #k #v #p #s (kn:knowledge k v p s)
  : prop
  = match kn with
    | Nothing -> False
    | Owns km -> forall k. kmap_owns_key km k

let pcm #k #v #p #s : pcm (knowledge k v p s) = {
  p = p0;
  comm = (fun k0 k1 ->
             match k0, k1 with
             | Nothing, _
             | _, Nothing -> ()
             | Owns m0, Owns m1 ->
               compose_kmaps_comm m0 m1);
  assoc = (fun k0 k1 k2 -> composable_assoc_l k0 k1 k2);
  assoc_r = (fun k0 k1 k2 -> composable_assoc_r k0 k1 k2);
  is_unit = (fun _ -> ());
  refine = full_knowledge;
}

let kmap_value_of (#k:eqtype)
                  (#v:Type)
                  (#p:preorder v)
                  (#s:_)
                  (m:kmap k v p s)
                  (key:k)
    = snd (Map.sel m key)

let kmap_update_key (#k:eqtype)
                    (#v:Type)
                    (#p:preorder v)
                    (#s:_)
                    (m:kmap k v p s)
                    (key:k)
                    (value:vhist p)
    = let p, _ = kmap_perm_of m key in
      let p' = p, Some (curval value) in
      Map.upd m key (p', value)

#push-options "--query_stats"

let frame_preserving_upd_lemma_refine
                   (#k:eqtype)
                    (#v:Type)
                    (#p:preorder v)
                    (#s:anchor_rel p)
                    (m:kmap k v p s)
                    (key:k)
                    (v1:vhist p {
                      kmap_owns_key m key /\
                      v1 `extends` kmap_value_of m key
                    })
                    (full_v:_{ pcm.refine full_v /\
                               compatible pcm (Owns m) full_v })
  : Lemma
    ( let Owns full_m = full_v in
      let m_res = kmap_update_key full_m key v1 in
      let res = Owns m_res in
      pcm.refine res)
  = ()

let frame_preserving_upd_lemma_compat
                   (#k:eqtype)
                    (#v:Type)
                    (#p:preorder v)
                    (#s:anchor_rel p)
                    (m:kmap k v p s)
                    (key:k)
                    (v1:vhist p {
                      kmap_owns_key m key /\
                      v1 `extends` kmap_value_of m key
                    })
                    (full_v:_{ pcm.refine full_v /\
                               compatible pcm (Owns m) full_v })
  : Lemma
    ( let Owns full_m = full_v in
      let m_res = kmap_update_key full_m key v1 in
      let res = Owns m_res in
      compatible pcm (Owns (kmap_update_key m key v1)) res)
  = let Owns full_m = full_v in
    let m_res = kmap_update_key full_m key v1 in
    let res = Owns m_res in
    let m' = kmap_update_key m key v1 in
    eliminate exists frame. composable (Owns m) frame /\ compose frame (Owns m) == full_v
    returns (compatible pcm (Owns (kmap_update_key m key v1)) res)
    with _. (
           assert (composable (Owns (kmap_update_key m key v1)) frame);
           match frame with
           | Nothing -> ()
           | Owns m_frame ->
             assert (not (has_some_ownership (kmap_perm_of m_frame key)));
             assert (Map.equal (compose_kmaps m_frame m') m_res)
    )

let frame_preserving_upd_lemma_upd
                    (#k:eqtype)
                    (#v:Type)
                    (#p:preorder v)
                    (#s:anchor_rel p)
                    (m:kmap k v p s)
                    (key:k)
                    (v1:vhist p {
                      kmap_owns_key m key /\
                      v1 `extends` kmap_value_of m key
                    })
                    (full_v:_{ pcm.refine full_v /\
                               compatible pcm (Owns m) full_v })
  : Lemma
    ( let Owns full_m = full_v in
      let m_res = kmap_update_key full_m key v1 in
      let res = Owns m_res in
      let m' = kmap_update_key m key v1 in
      forall (frame:_{composable (Owns m) frame}). {:pattern composable (Owns m) frame}
        composable (Owns m') frame /\
        (compose (Owns m) frame == full_v ==> compose (Owns m') frame == res))
  = let Owns full_m = full_v in
    let m_res = kmap_update_key full_m key v1 in
    let res = Owns m_res in
    let m' = kmap_update_key m key v1 in
    introduce forall (frame:_{composable (Owns m) frame}).
                composable (Owns m') frame /\
                (compose (Owns m) frame == full_v ==> compose (Owns m') frame == res)
      with (
        introduce _ /\ _
        with ()
        and introduce _ ==> _
        with _. (
          assert (compose (Owns m) frame == full_v);
          match frame with
          | Nothing -> ()
          | Owns m_frame ->
            assert (not (has_some_ownership (kmap_perm_of m_frame key)));
            let m_res' = compose_kmaps m_frame m' in
            introduce forall key'.
              Map.sel m_res' key' == Map.sel m_res key'
            with (
              if key <> key'
              then (
                ()
              )
              else (
                ()
              )
            );
            assert (Map.equal (compose_kmaps m_frame m') m_res)
        )
      )

let update_key_hist (#k:eqtype)
                    (#v:Type)
                    (#p:preorder v)
                    (#s:anchor_rel p)
                    (m:kmap k v p s)
                    (key:k)
                    (v1:vhist p {
                      kmap_owns_key m key /\
                      v1 `extends` kmap_value_of m key
                    })
  : frame_preserving_upd pcm (Owns m) (Owns (kmap_update_key m key v1))
  = fun full_v ->
      assert (full_knowledge full_v);
      assert (compatible pcm (Owns m) full_v);
      let Owns full_m = full_v in
      let m_res = kmap_update_key full_m key v1 in
      let res = Owns m_res in
      frame_preserving_upd_lemma_refine m key v1 full_v;
      frame_preserving_upd_lemma_compat m key v1 full_v;
      frame_preserving_upd_lemma_upd m key v1 full_v;
      res

let kmap_update_key_value (#k:eqtype)
                          (#v:Type)
                          (#p:preorder v)
                          (#s:anchor_rel p)
                          (m:kmap k v p s)
                          (key:k)
                          (value:v { curval (kmap_value_of m key) `p` value })
  : m':kmap k v p s {
                    curval (kmap_value_of m' key) == value /\
                    kmap_value_of m' key `extends` kmap_value_of m key
                  }
  = let v = kmap_value_of m key in
    kmap_update_key m key (extend_history v value)

let update_key (#k:eqtype)
               (#v:Type)
               (#p:preorder v)
               (#s:anchor_rel p)
               (m:kmap k v p s)
               (key:k)
               (v1:v {
                 kmap_owns_key m key /\ //if you have full ownership of key
                 curval (kmap_value_of m key) `p` v1 //you can update it wrt the preorder only
               })
  : frame_preserving_upd pcm (Owns m) (Owns (kmap_update_key_value m key v1))
  = let v1':vhist p = extend_history (kmap_value_of m key) v1 in
    coerce_eq () (update_key_hist m key v1')


// let frame_preserving_upd_lemma_refine
//                    (#k:eqtype)
//                     (#v:Type)
//                     (#p:preorder v)
//                     (#s:anchor_rel p)
//                     (m:kmap k v p s)
//                     (key:k)
//                     (v1:vhist p {
//                       kmap_owns_key m key /\
//                       v1 `extends` kmap_value_of m key
//                     })
//                     (full_v:_{ pcm.refine full_v /\
//                                compatible pcm (Owns m) full_v })
//   : Lemma
//     ( let Owns full_m = full_v in
//       let m_res = kmap_update_key full_m key v1 in
//       let res = Owns m_res in
//       pcm.refine res)
//   = ()

// let frame_preserving_upd_lemma_compat
//                    (#k:eqtype)
//                     (#v:Type)
//                     (#p:preorder v)
//                     (#s:anchor_rel p)
//                     (m:kmap k v p s)
//                     (key:k)
//                     (v1:vhist p {
//                       kmap_owns_key m key /\
//                       v1 `extends` kmap_value_of m key
//                     })
//                     (full_v:_{ pcm.refine full_v /\
//                                compatible pcm (Owns m) full_v })
//   : Lemma
//     ( let Owns full_m = full_v in
//       let m_res = kmap_update_key full_m key v1 in
//       let res = Owns m_res in
//       compatible pcm (Owns (kmap_update_key m key v1)) res)
//   = let Owns full_m = full_v in
//     let m_res = kmap_update_key full_m key v1 in
//     let res = Owns m_res in
//     let m' = kmap_update_key m key v1 in
//     eliminate exists frame. composable (Owns m) frame /\ compose frame (Owns m) == full_v
//     returns (compatible pcm (Owns (kmap_update_key m key v1)) res)
//     with _. (
//            assert (composable (Owns (kmap_update_key m key v1)) frame);
//            match frame with
//            | Nothing -> ()
//            | Owns m_frame ->
//              assert (not (has_some_ownership (kmap_perm_of m_frame key)));
//              assert (Map.equal (compose_kmaps m_frame m') m_res)
//     )

// let frame_preserving_upd_lemma_upd
//                     (#k:eqtype)
//                     (#v:Type)
//                     (#p:preorder v)
//                     (#s:anchor_rel p)
//                     (m:kmap k v p s)
//                     (key:k)
//                     (v1:vhist p {
//                       kmap_owns_key m key /\
//                       v1 `extends` kmap_value_of m key
//                     })
//                     (full_v:_{ pcm.refine full_v /\
//                                compatible pcm (Owns m) full_v })
//   : Lemma
//     ( let Owns full_m = full_v in
//       let m_res = kmap_update_key full_m key v1 in
//       let res = Owns m_res in
//       let m' = kmap_update_key m key v1 in
//       forall (frame:_{composable (Owns m) frame}). {:pattern composable (Owns m) frame}
//         composable (Owns m') frame /\
//         (compose (Owns m) frame == full_v ==> compose (Owns m') frame == res))
//   = let Owns full_m = full_v in
//     let m_res = kmap_update_key full_m key v1 in
//     let res = Owns m_res in
//     let m' = kmap_update_key m key v1 in
//     introduce forall (frame:_{composable (Owns m) frame}).
//                 composable (Owns m') frame /\
//                 (compose (Owns m) frame == full_v ==> compose (Owns m') frame == res)
//       with (
//         introduce _ /\ _
//         with ()
//         and introduce _ ==> _
//         with _. (
//           assert (compose (Owns m) frame == full_v);
//           match frame with
//           | Nothing -> ()
//           | Owns m_frame ->
//             assert (not (has_some_ownership (kmap_perm_of m_frame key)));
//             let m_res' = compose_kmaps m_frame m' in
//             introduce forall key'.
//               Map.sel m_res' key' == Map.sel m_res key'
//             with (
//               if key <> key'
//               then (
//                 ()
//               )
//               else (
//                 ()
//               )
//             );
//             assert (Map.equal (compose_kmaps m_frame m') m_res)
//         )
//       )

let kmap_owns_anchored_key (#k:eqtype)
                           (#v:Type)
                           (#p:preorder v)
                           (#s:anchor_rel p)
                           (m:kmap k v p s)
                           (key:k)
    = fst (kmap_perm_of m key) == Some full /\
      None? (snd (kmap_perm_of m key))


// let update_anchored_key_hist (#k:eqtype)
//                              (#v:Type)
//                              (#p:preorder v)
//                              (#s:anchor_rel p)
//                              (m:kmap k v p s)
//                              (key:k)
//                              (v1:vhist p {
//                                kmap_owns_anchored_key m key /\
//                                v1 `extends` kmap_value_of m key
//                              })
//   : frame_preserving_upd pcm (Owns m) (Owns (kmap_update_key m key v1))
//   = fun full_v ->
//       assert (full full_v);
//       assert (compatible pcm (Owns m) full_v);
//       let Owns full_m = full_v in
//       let m_res = kmap_update_key full_m key v1 in
//       let res = Owns m_res in
//       frame_preserving_upd_lemma_refine m key v1 full_v;
//       frame_preserving_upd_lemma_compat m key v1 full_v;
//       frame_preserving_upd_lemma_upd m key v1 full_v;
//       res


// let ksnapshot (#k:eqtype) (#v:Type0) (#c:preorder v)
//              (m: kmap k v c)
//   : kmap k v c
//   = map_literal (fun k -> None, snd (Map.sel m k))

// let all_perms_ok (#k:eqtype)
//                  (#v:Type)
//                  (#p:preorder v)
//                  (m:kmap k v p)
//   = forall k. perm_opt_composable (kmap_perm_of m k) None


// let snapshot_lemma (#k:eqtype)
//                    (#v:Type)
//                    (#p:preorder v)
//                    (m:kmap k v p)
//   : Lemma (requires all_perms_ok m)
//           (ensures Owns m `composable` Owns (ksnapshot m))
//   = ()


// let snapshot_dup_lemma (#k:eqtype)
//                        (#v:Type)
//                        (#p:preorder v)
//                        (m:kmap k v p)
//   : Lemma (requires all_perms_ok m)
//           (ensures Owns (ksnapshot m) `composable` Owns (ksnapshot m))
//   = ()

// let update_snapshot_lemma (#k:eqtype)
//                           (#v:Type)
//                           (#p:preorder v)
//                           (m0 m1:kmap k v p)
//                           (key:k)
//   : Lemma (requires composable (Owns m0) (Owns m1) /\
//                     kmap_owns_key m0 key)
//           (ensures composable (Owns m0) (Owns (kmap_update_key m1 key (kmap_value_of m0 key))))
//   = ()

// ////////////////////////////////////////////////////////////////////////////////

// let tmap (k:eqtype) (v:Type0) (c:preorder v) = Map.t k (hist c)

// val t (k:eqtype) (v:Type0) (c:preorder v) : Type0

// val k_of (#k:eqtype) (#v:Type0) (#c:preorder v)
//          (t:t k v c)
//          (knowledge: knowledge k v c)
//   : vprop

// val share  (#o:_)
//            (#k:eqtype) (#v:Type0) (#c:preorder v)
//            (#m0 :kmap k v c)
//            (#m1: kmap k v c { kmap_composable m0 m1 })
//            (t:t k v c)
//   : STGhostT unit o
//     (k_of t (Owns (compose_kmaps m0 m1)))
//     (fun _ -> k_of t (Owns m0) `star` k_of t (Owns m1))

// val gather (#o:_)
//            (#k:eqtype) (#v:Type0) (#c:preorder v)
//            (#m0 #m1: kmap k v c)
//            (t:t k v c)
//   : STGhostT (_:unit { kmap_composable m0 m1 }) o
//     (k_of t (Owns m0) `star` k_of t (Owns m1))
//     (fun _ -> k_of t (Owns (compose_kmaps m0 m1)))

// let snapshot (#k:eqtype) (#v:Type0) (#c:preorder v)
//              (m: kmap k v c)
//   : Map.t k v
//   = map_literal (fun k -> curval (snd (Map.sel m k)))

// val global_snapshot (#k:eqtype) (#v:Type0) (#c:preorder v)
//                     (t:t k v c)
//                     ([@@@smt_fallback] m: Map.t k v)
//   : vprop
//   // = exists_ (fun (km:kmap k v c) ->
//   //       pure (snapshot km == m) `star`
//   //       k_of t (Owns (ksnapshot km)))

// val take_snapshot (#o:_)
//                   (#k:eqtype) (#v:Type0) (#c:preorder v)
//                   (#m: kmap k v c)
//                   (t:t k v c)
//   : STGhostT unit o
//     (k_of t (Owns m))
//     (fun _ -> k_of t (Owns m) `star` global_snapshot t (snapshot m))

// val owns_key (#k:eqtype) (#v:Type0) (#c:preorder v)
//              (t:t k v c)
//              (key:k)
//              ([@@@smt_fallback]perm:perm)
//              ([@@@smt_fallback]value:v)
//  : vprop
//   // = exists_ (fun (m:kmap k v c) ->
//   //      pure ((forall key'. (key<>key' ==> fst (Map.sel m key') == None)) /\
//   //            (match Map.sel m key with
//   //             | None, _ -> False
//   //             | Some p, h ->
//   //               perm == p /\
//   //               curval h == value)) `star`
//   //      k_of t (Owns m))

// val snapshot_of_key (#k:eqtype) (#v:Type0) (#c:preorder v)
//                     (t:t k v c)
//                     (key:k)
//                     ([@@@smt_fallback]value:v)
//  : vprop
//   // = exists_ (fun (m:kmap k v c) ->
//   //      pure ((forall key'. fst (Map.sel m key') == None) /\
//   //            (match Map.sel m key with
//   //             | Some _, _ -> False
//   //             | None, h -> curval h == value)) `star`
//   //      k_of t (Owns m))

// val local_snapshot (#o:_)
//                    (#k:eqtype) (#v:Type0) (#c:preorder v)
//                    (#key:k) (#frac:_) (#value:v)
//                    (t:t k v c)
//   : STGhostT unit o
//     (owns_key t key frac value)
//     (fun _ -> owns_key t key frac value `star` snapshot_of_key t key value)

// val dup_snapshot (#o:_)
//                  (#k:eqtype) (#v:Type0) (#c:preorder v)
//                  (#key:k) (#value:v)
//                  (t:t k v c)
//   : STGhostT unit o
//     (snapshot_of_key t key value)
//     (fun _ -> snapshot_of_key t key value `star` snapshot_of_key t key value)

// val update (#o:_)
//            (#k:eqtype) (#v:Type0) (#c:preorder v)
//            (#key:k) (#value:v)
//            (t:t k v c)
//            (value':v {c value value'})
//   : STGhostT unit o
//     (owns_key t key full_perm value)
//     (fun _ -> owns_key t key full_perm value')

// val update_global_snapshot (#o:_)
//                            (#k:eqtype) (#v:Type0) (#c:preorder v)
//                            (#key:k) (#frac:_) (#value:v)
//                            (t:t k v c)
//                            (m:Map.t k v)
//   : STGhostT unit o
//     (owns_key t key frac value `star` global_snapshot t m)
//     (fun _ -> owns_key t key frac value `star` global_snapshot t (Map.upd m key value))


// val dup_global_snapshot (#o:_) (#k:eqtype) (#v:Type0) (#c:preorder v) (#m: Map.t k v)
//                         (t:t k v c)
//   : STGhostT unit o
//     (global_snapshot t m)
//     (fun _ -> global_snapshot t m `star` global_snapshot t m)