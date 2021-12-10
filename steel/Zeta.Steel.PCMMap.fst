module Zeta.Steel.PCMMap
open FStar.Map
open FStar.PCM
open Zeta.Steel.Util

let map (k:eqtype) (v:Type) = m:Map.t k v { Map.domain m `Set.equal` Set.complement Set.empty }
let composable_maps (#a:_) (#k:eqtype)
                    (p:pcm a)
                    (m0 m1: map k a)
  : prop
  = forall k. Map.sel m0 k `composable p` Map.sel m1 k

let compose_maps (#a:_) (#k:eqtype)
                 (p:pcm a)
                 (m0:map k a)
                 (m1:map k a { composable_maps p m0 m1 })
  : map k a
  = map_literal (fun k ->
                   Map.sel m0 k `op p` Map.sel m1 k)

let composable_maps_comm #k #a
                    (p:pcm a)
                    (m0 m1: map k a)
  : Lemma (composable_maps p m0 m1 <==>
           composable_maps p m1 m0)
  = ()


let compose_maps_comm #k #a
                    (p:pcm a)
                    (m0 m1: map k a)
  : Lemma
    (requires composable_maps p m0 m1)
    (ensures compose_maps p m0 m1 == compose_maps p m1 m0)
  = let m01 = compose_maps p m0 m1 in
    let m10 = compose_maps p m1 m0 in
    introduce forall key.
         Map.sel m01 key == Map.sel m10 key
    with ( p.comm (Map.sel m0 key) (Map.sel m1 key) );
    assert (Map.equal m01 m10)

let composable_maps_assoc_l #k #a
                          (p:pcm a)
                          (m0 m1 m2: map k a)
  : Lemma
    (requires
      composable_maps p m1 m2 /\
      composable_maps p m0 (compose_maps p m1 m2))
    (ensures
      composable_maps p m0 m1 /\
      composable_maps p (compose_maps p m0 m1) m2 /\
      compose_maps p (compose_maps p m0 m1) m2 ==
      compose_maps p m0 (compose_maps p m1 m2))
  = introduce forall key.
      composable p (Map.sel m0 key) (Map.sel m1 key)
    with ( p.assoc (Map.sel m0 key) (Map.sel m1 key) (Map.sel m2 key) );
    let m01 = compose_maps p m0 m1 in
    introduce forall key.
      composable p (Map.sel m01 key) (Map.sel m2 key)
    with ( p.assoc (Map.sel m0 key) (Map.sel m1 key) (Map.sel m2 key) );
    let m012 = compose_maps p m01 m2 in
    let m012' = compose_maps p m0 (compose_maps p m1 m2) in
    introduce forall key.
      Map.sel m012 key == Map.sel m012' key
    with ( p.assoc (Map.sel m0 key) (Map.sel m1 key) (Map.sel m2 key) );
    assert (Map.equal
                 (compose_maps p (compose_maps p m0 m1) m2)
                 (compose_maps p m0 (compose_maps p m1 m2)))

let composable_maps_assoc_r #k #a
                          (p:pcm a)
                          (m0 m1 m2: map k a)
  : Lemma
    (requires
      composable_maps p m0 m1 /\
      composable_maps p (compose_maps p m0 m1) m2)
    (ensures
      composable_maps p m1 m2 /\
      composable_maps p m0 (compose_maps p m1 m2) /\
      compose_maps p (compose_maps p m0 m1) m2 ==
      compose_maps p m0 (compose_maps p m1 m2))
  = introduce forall key.
      composable p (Map.sel m1 key) (Map.sel m2 key)

    with ( p.assoc_r (Map.sel m0 key) (Map.sel m1 key) (Map.sel m2 key) );
    let m12 = compose_maps p m1 m2 in
    introduce forall key.
      composable p (Map.sel m0 key) (Map.sel m12 key)
    with ( p.assoc_r (Map.sel m0 key) (Map.sel m1 key) (Map.sel m2 key) );
    let m012 = compose_maps p (compose_maps p m0 m1) m2 in
    let m012' = compose_maps p m0 (compose_maps p m1 m2) in
    introduce forall key.
      Map.sel m012 key == Map.sel m012' key
    with ( p.assoc_r (Map.sel m0 key) (Map.sel m1 key) (Map.sel m2 key) );
    assert (Map.equal m012 m012')

let pcm'_map_of_pcm (#a:_) (k:eqtype) (p:pcm a)
  : pcm' (option (map k a))
  = {
       composable =
         (fun m0 m1 ->
           match m0, m1 with
           | None, _
           | _, None -> True
           | Some m0, Some m1 ->
             composable_maps p m0 m1);
       op = (fun m0 m1 ->
              match m0, m1 with
              | None, m
              | m, None -> m
              | Some m0, Some m1 ->
                Some (compose_maps p m0 m1));
       one = None;
    }

let pcm_map_of_pcm (#a:_) (k:eqtype) (p:pcm a)
  : pcm (option (map k a))
  = {
       p = pcm'_map_of_pcm k p;
       comm = (fun m0 m1 ->
                 match m0, m1 with
                 | None, _
                 | _, None -> ()
                 | Some m0, Some m1 -> compose_maps_comm p m0 m1);
       assoc = (fun m0 m1 m2 ->
                  match m0, m1, m2 with
                  | Some m0, Some m1, Some m2 ->
                    composable_maps_assoc_l p m0 m1 m2
                  | _ -> ());
       assoc_r = (fun m0 m1 m2 ->
                  match m0, m1, m2 with
                  | Some m0, Some m1, Some m2 ->
                    composable_maps_assoc_r p m0 m1 m2
                  | _ -> ());
       is_unit = (fun _ -> ());
       refine = (fun a -> Some? a /\ (forall k. p.refine (Map.sel (Some?.v a) k)))
    }

let compatible_pointwise #a #k
                         (p:pcm a)
                         (m0 m1:map k a)
  : Lemma
    (requires compatible (pcm_map_of_pcm k p) (Some m0) (Some m1))
    (ensures forall k. compatible p (Map.sel m0 k) (Map.sel m1 k))
  = let pcm' = pcm_map_of_pcm k p in
    introduce forall k. compatible p (Map.sel m0 k) (Map.sel m1 k)
    with (
      eliminate exists frame.
        composable pcm' (Some m0) frame /\ op pcm' frame (Some m0) == (Some m1)
      returns _
      with _. (
        introduce exists (frame:a).
                         composable p
                                    (Map.sel m0 k)
                                    frame /\
                         op p frame (Map.sel m0 k) == Map.sel m1 k
        with (match frame with None -> p.p.one | Some m -> Map.sel m k)
        and ( p.is_unit (Map.sel m0 k);
              p.comm p.p.one (Map.sel m0 k) ) ))


let compatible_pointwise_upd #a (#k:eqtype)
                             (p:pcm a)
                             (v1 full_v1:a)
                             (m0 full_m0:map k a)
                             (key:k)
  : Lemma
    (requires
      compatible p v1 full_v1 /\
      compatible (pcm_map_of_pcm k p) (Some m0) (Some full_m0))
    (ensures
      compatible (pcm_map_of_pcm k p) (Some (Map.upd m0 key v1))
                                      (Some (Map.upd full_m0 key full_v1)))
  = compatible_pointwise p m0 full_m0;
    assert (compatible p (Map.sel m0 key) (Map.sel full_m0 key));
    let m1 = (Map.upd m0 key v1) in
    let full_m1 = (Map.upd full_m0 key full_v1) in
    let p' = pcm_map_of_pcm k p in
    eliminate exists (frame_m0:_). composable p' (Some m0) frame_m0 /\ op p' frame_m0 (Some m0) == Some full_m0
    returns _
    with _. (
    eliminate exists (frame0:_). composable p v1 frame0 /\ op p frame0 v1 == full_v1
    returns _
    with _. (
      introduce exists (frame:_).
      composable p' (Some m1) frame /\ op p' frame (Some m1) == (Some full_m1)
    with (
      match frame_m0 with
      | None -> Some (Map.upd (Map.const p.p.one) key frame0)
      | Some frame_m0 -> Some (Map.upd frame_m0 key frame0)
    )
    and (
      match frame_m0 with
      | None ->
        let w = Map.upd (Map.const p.p.one) key frame0 in
        introduce forall v.
          composable p p.p.one v /\
          composable p v p.p.one /\
          op p p.p.one v == v /\
          op p v p.p.one == v
        with ( p.is_unit v; p.comm v p.p.one );
        introduce forall k.
          Map.sel m1 k `composable p` Map.sel w k
        with (
          if k <> key
          then (
            p.is_unit (Map.sel m1 k)
          )
        );
        assert (composable_maps p m1 w);
        introduce forall k.
          Map.sel (compose_maps p w m1) k == Map.sel full_m1 k
        with (
            p.is_unit (Map.sel m1 k)
        );
        assert (Map.equal (compose_maps p w m1) full_m1)
      | Some frame_m0 ->
        let w = Map.upd frame_m0 key frame0 in
        assert (Map.equal (compose_maps p w m1) full_m1)
    )))


let lift_fp #a (#k:eqtype) (p:pcm a)
            (m0 full_m0:map k a)
            (v1 full_v1:a)
            (key:k)
  : Lemma
    (requires (
      let v0 = Map.sel m0 key in
      let full_v0 = Map.sel full_m0 key in
      let m1 = Map.upd m0 key v1 in
      let full_m1 = Map.upd full_m0 key full_v1 in
      (forall (frame:a{composable p v0 frame}). {:pattern composable p v0 frame}
         composable p v1 frame /\
         (op p v0 frame == full_v0 ==>
          op p v1 frame == full_v1))))
    (ensures (
      let v0 = Map.sel m0 key in
      let full_v0 = Map.sel full_m0 key in
      let m1 = Map.upd m0 key v1 in
      let full_m1 = Map.upd full_m0 key full_v1 in
      let p' = pcm_map_of_pcm k p in
      (forall (frame:_{composable p' (Some m0) frame}).
         composable p' (Some m1) frame /\
         (op p' (Some m0) frame == (Some full_m0) ==>
          op p' (Some m1) frame == (Some full_m1)))))
    = let v0 = Map.sel m0 key in
      let full_v0 = Map.sel full_m0 key in
      let m1 = Map.upd m0 key v1 in
      let full_m1 = Map.upd full_m0 key full_v1 in
      let p' = pcm_map_of_pcm k p in
      introduce forall (frame:_{composable p' (Some m0) frame}).
         composable p' (Some m1) frame /\
         (op p' (Some m0) frame == (Some full_m0) ==>
          op p' (Some m1) frame == (Some full_m1))
      with (
        introduce _ /\ _
        with ()
        and ( introduce _ ==> _
              with _. (
                match frame with
                | None ->
                  assert (m0 == full_m0);
                  p.is_unit v0;
                  p.is_unit v1;
                  assert (composable p v0 p.p.one);
                  assert (v1 == full_v1);
                  assert (m1 `Map.equal` full_m1)
                | Some frame' ->
                  // assert (composable p' (Some m0) (Some frame'));
                  // assert (composable p (Map.sel m0 key) (Map.sel frame' key));
                  // assert (Map.sel m0 key == v0);
                  // assert (composable p v0 (Map.sel frame' key));
                  assert (compose_maps p m1 frame' `Map.equal` full_m1)
              )
        )
      )

let lift_fp_upd #a #k (#p:pcm a)
                (v0 v1:a)
                (f:frame_preserving_upd p v0 v1)
                (m0:map k a)
                (key:k { Map.sel m0 key == v0 })
  : frame_preserving_upd (pcm_map_of_pcm k p)
                         (Some m0)
                         (Some (Map.upd m0 key v1))
  = fun (Some full_m0) ->
          let p' = pcm_map_of_pcm k p in
          let full_v0 = Map.sel full_m0 key in
          assert (compatible (pcm_map_of_pcm _ p) (Some m0) (Some full_m0));
          assert (p.refine full_v0);
          compatible_pointwise #a #k p m0 full_m0;
          assert (compatible p v0 full_v0);
          let full_v1 = f full_v0 in
          let full_m1 = Map.upd full_m0 key full_v1 in
          assert (p'.refine (Some full_m1));
          compatible_pointwise_upd p v1 full_v1 m0 full_m0 key;
          let m1 = Map.upd m0 key v1 in
          assert (compatible p' (Some m1) (Some full_m1));
          lift_fp p m0 full_m0 v1 full_v1 key;
          Some full_m1

let lift_composable #k #a (p:pcm a)
                          (v0 v1:a)
                          (m0 m1:map k a)
                          (key:k)
 : Lemma (requires composable p v0 v1 /\
                   composable (pcm_map_of_pcm k p) (Some m0) (Some m1))
         (ensures
                  composable (pcm_map_of_pcm k p) (Some (Map.upd m0 key v0)) (Some (Map.upd m1 key v1)))
 = ()
