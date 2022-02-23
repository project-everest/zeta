module Zeta.Steel.EpochMap

module G = FStar.Ghost
module U32 = FStar.UInt32

open Steel.FractionalPermission
open Steel.Memory
open Steel.ST.Effect.Ghost
open Steel.ST.Effect.Atomic
open Steel.ST.Effect
open Steel.ST.Util
module R = Steel.ST.Reference
module ETbl = Steel.ST.EphemeralHashtbl

module M = Zeta.Steel.ThreadStateModel

inline_for_extraction
let hash : ETbl.hash_fn M.epoch_id = fun eid -> eid

noeq
type tbl #v #c vp = {
  etbl : ETbl.tbl #M.epoch_id #v #c vp hash;
  high : R.ref M.epoch_id
}

let repr_to_eht_repr (#a:Type0) (m:repr a) : PartialMap.t M.epoch_id a =
  PartialMap.literal (fun x -> Some (Map.sel m x))

let high_epoch_id_prop
  (#v #c:Type0)
  (default_value:c)
  (m:repr c)
  (b:borrows v)
  (e:M.epoch_id)
  : prop
  = (forall (e':M.epoch_id). U32.v e < U32.v e' ==> Map.sel m e' == default_value) /\
    (forall (e':M.epoch_id). PartialMap.contains b e' ==> U32.v e' <= U32.v e)

[@@ __reduce__]
let high_epoch_id_pred
  (#v #c:Type0)
  (default_value:c)
  (m:repr c)
  (b:borrows v)
  (r:R.ref M.epoch_id)
  : M.epoch_id -> vprop
  = fun e ->
    R.pts_to r full_perm e
      `star`
    pure (high_epoch_id_prop default_value m b e)

[@@ __reduce__]
let perm #v #c #cp t default_value m b =
  ETbl.tperm t.etbl (repr_to_eht_repr m) b
    `star`
  exists_ (high_epoch_id_pred default_value m b t.high)

let create #v #c #vp n init =
  let etbl = ETbl.create_v vp hash n init in
  let high = R.alloc 0ul in
  intro_pure (high_epoch_id_prop (G.reveal init)
                                 (Map.const (G.reveal init))
                                 (empty_borrows #v)
                                 0ul);
  let r = { etbl = etbl; high = high } in
  assert (PartialMap.equal (PartialMap.const M.epoch_id (G.reveal init))
                           (repr_to_eht_repr (Map.const #M.epoch_id #c init)));
  rewrite (ETbl.tperm _ _ _)
          (ETbl.tperm r.etbl
                      (repr_to_eht_repr (Map.const (G.reveal init)))
                      empty_borrows);
  rewrite (R.pts_to _ _ _ `star` pure _)
          (high_epoch_id_pred (G.reveal init)
                              (Map.const (G.reveal init))
                              empty_borrows
                              r.high
                              0ul);
  intro_exists 0ul (high_epoch_id_pred _ _ _ _);
  return r

let free #v #c #vp #init #m #b t =
  let w = elim_exists () in
  elim_pure (high_epoch_id_prop (G.reveal init) m b w);
  ETbl.free t.etbl;
  R.free t.high

let get #v #c #vp #init #m #b a i =
  let w = elim_exists () in
  elim_pure (high_epoch_id_prop (G.reveal init) m b w);
  let high_value = R.read a.high in
  let r = high_value `U32.lt` i in
  if r returns ST _
                  _
                  (get_post init m b a i)
                  (requires ~ (PartialMap.contains b i))
                  (ensures fun res -> Fresh? res ==> Map.sel m i == G.reveal init)

  then begin
    let ret = Fresh in
    intro_pure (high_epoch_id_prop (G.reveal init) m b w);
    intro_exists (G.reveal w)
                 (high_epoch_id_pred (G.reveal init) m b a.high);
    rewrite (ETbl.tperm a.etbl (repr_to_eht_repr m) b
               `star`
             exists_ (high_epoch_id_pred (G.reveal init) m b a.high))
            (get_post init m b a i ret);
    return ret
  end
  else begin
    let x = ETbl.get a.etbl i in
    match x returns ST _
                       (ETbl.get_post (repr_to_eht_repr m) b a.etbl i x
                          `star`
                        R.pts_to a.high Steel.FractionalPermission.full_perm w)
                       (get_post init m b a i)
                       (requires ~ (PartialMap.contains b i))
                       (ensures fun res -> Fresh? res ==> Map.sel m i == G.reveal init) with
    | ETbl.Missing j ->
      let ret = NotFound in      
      rewrite (ETbl.get_post (repr_to_eht_repr m) b a.etbl i (ETbl.Missing j))
              (ETbl.tperm a.etbl (repr_to_eht_repr m) b
                 `star`
               pure (ETbl.map_contains_prop j (repr_to_eht_repr m)));
      elim_pure (ETbl.map_contains_prop j (repr_to_eht_repr m));
      intro_pure (high_epoch_id_prop (G.reveal init) m b w);
      intro_exists (G.reveal w)
                   (high_epoch_id_pred (G.reveal init) m b a.high);
      rewrite (ETbl.tperm a.etbl (repr_to_eht_repr m) b
                 `star`
               exists_ (high_epoch_id_pred (G.reveal init) m b a.high))
              (get_post init m b a i ret);
      return ret
    | ETbl.Absent ->
      let ret = NotFound in      
      rewrite (ETbl.get_post (repr_to_eht_repr m) b a.etbl i ETbl.Absent)
              (ETbl.tperm a.etbl (repr_to_eht_repr m) b);
      intro_pure (high_epoch_id_prop (G.reveal init) m b w);
      intro_exists (G.reveal w)
                   (high_epoch_id_pred (G.reveal init) m b a.high);
      rewrite (ETbl.tperm a.etbl (repr_to_eht_repr m) b
                 `star`
               exists_ (high_epoch_id_pred (G.reveal init) m b a.high))
              (get_post init m b a i ret);
      return ret
    | ETbl.Present x ->
      let ret = Found x in
      assert (Some? (PartialMap.sel (repr_to_eht_repr m) i));
      rewrite (ETbl.get_post (repr_to_eht_repr m) b a.etbl i (ETbl.Present x))
              (ETbl.tperm a.etbl (repr_to_eht_repr m) (PartialMap.upd b i x)
                 `star`
               vp i x (Map.sel m i));
      intro_pure (high_epoch_id_prop (G.reveal init) m (PartialMap.upd b i x) w);
      intro_exists
        (G.reveal w)
        (high_epoch_id_pred (G.reveal init) m (PartialMap.upd b i x) a.high);
      rewrite (perm a init m (PartialMap.upd b i x)
                 `star`
               vp i x (Map.sel m i))
              (get_post init m b a i ret);
      return ret
  end

let put #v #c #vp #init #m #b a i x content =
  let w = elim_exists () in
  elim_pure (high_epoch_id_prop (G.reveal init) m b w);
  ETbl.put a.etbl i x content;
  assert (PartialMap.equal (PartialMap.upd (repr_to_eht_repr m) i content)
                           (repr_to_eht_repr (Map.upd m i content)));
  rewrite (ETbl.tperm _ _ _)
          (ETbl.tperm a.etbl
                      (repr_to_eht_repr (Map.upd m i content))
                      (PartialMap.remove b i));
  let high = R.read a.high in
  let r = high `U32.lt` i in
  if r
  then begin
    R.write a.high i;
    intro_pure (high_epoch_id_prop (G.reveal init)
                                   (Map.upd m i content)
                                   (PartialMap.remove b i)
                                   i);
    intro_exists i (high_epoch_id_pred (G.reveal init)
                                       (Map.upd m i content)
                                       (PartialMap.remove b i)
                                       a.high)
  end
  else begin
    intro_pure (high_epoch_id_prop (G.reveal init)
                                   (Map.upd m i content)
                                   (PartialMap.remove b i)
                                   w);
    intro_exists (G.reveal w) (high_epoch_id_pred (G.reveal init)
                                                  (Map.upd m i content)
                                                  (PartialMap.remove b i)
                                                  a.high)
  end

let ghost_put #_ #v #c #vp #init #m #b a i x content =
  let w = elim_exists () in
  elim_pure (high_epoch_id_prop (G.reveal init) m b w);
  ETbl.ghost_put a.etbl i x content;
  assert (PartialMap.equal (PartialMap.upd (repr_to_eht_repr m) i content)
                           (repr_to_eht_repr (Map.upd m i content)));
  rewrite (ETbl.tperm _ _ _)
          (ETbl.tperm a.etbl
                      (repr_to_eht_repr (Map.upd m i content))
                      (PartialMap.remove b i));
  intro_pure (high_epoch_id_prop (G.reveal init)
                                 (Map.upd m i content)
                                 (PartialMap.remove b i)
                                 w);
  intro_exists
    (G.reveal w)
    (high_epoch_id_pred (G.reveal init) (Map.upd m i content) (PartialMap.remove b i) a.high)

let reclaim #v #c #vp #init #m #b a i =
  let w = elim_exists () in
  elim_pure (high_epoch_id_prop (G.reveal init) m b w);
  let _ = ETbl.remove a.etbl i in
  intro_pure (high_epoch_id_prop (G.reveal init) m (PartialMap.remove b i) w);
  intro_exists
    (G.reveal w)
    (high_epoch_id_pred (G.reveal init) m (PartialMap.remove b i) a.high)
