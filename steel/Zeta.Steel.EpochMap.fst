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

//
//TODO: instantiate this hash function
//
assume val hash : ETbl.hash_fn M.epoch_id

noeq
type tbl #v #c vp = {
  etbl : ETbl.tbl #M.epoch_id #v #c vp hash;
  high : R.ref M.epoch_id
}

let repr_to_eht_repr (#a:Type0) (m:repr a) : PartialMap.t M.epoch_id a =
  PartialMap.literal (fun x -> Some (Map.sel m x))

let high_epoch_id_prop (#v #c:Type0) (default_value:c) (m:repr c) (b:borrows v) (e:M.epoch_id)
  : prop
  = (forall (e':M.epoch_id). U32.v e < U32.v e' ==> Map.sel m e' == default_value) /\
    (forall (e':M.epoch_id). PartialMap.contains e' b ==> U32.v e' <= U32.v e)

[@@ __reduce__]
let high_epoch_id_pred (#v #c:Type0) (default_value:c) (m:repr c) (b:borrows v) (r:R.ref M.epoch_id)
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
  intro_pure (high_epoch_id_prop (G.reveal init) (Map.const (G.reveal init)) (empty_borrows #v) 0ul);
  let r = { etbl = etbl; high = high } in
  assert (PartialMap.equal (PartialMap.const M.epoch_id (G.reveal init))
                           (repr_to_eht_repr (Map.const #M.epoch_id #c init)));
  rewrite (ETbl.tperm _ _ _)
          (ETbl.tperm r.etbl (repr_to_eht_repr (Map.const (G.reveal init))) empty_borrows);
  rewrite (R.pts_to _ _ _ `star` pure _)
          (high_epoch_id_pred (G.reveal init) (Map.const (G.reveal init)) (empty_borrows #v) r.high 0ul);
  intro_exists 0ul (high_epoch_id_pred _ _ _ _);
  return r

let free #v #c #vp #init #m #b t =
  let w = elim_exists () in
  elim_pure (high_epoch_id_prop (G.reveal init) m b (G.reveal w));
  ETbl.free t.etbl;
  R.free t.high

let get #v #c #vp #init #m #b a i =
  let w = elim_exists () in
  elim_pure (high_epoch_id_prop (G.reveal init) m b (G.reveal w));
  let high_value = R.read a.high in
  let r = high_value `U32.lt` i in
  if r returns ST (get_result v)
                  _
                  (get_post init m b a i)
                  (requires ~ (PartialMap.contains i b))
                  (ensures fun res -> Fresh? res ==> Map.sel m i == G.reveal init)

  then begin
    let ret = Fresh in
    intro_pure (high_epoch_id_prop (G.reveal init) m b (G.reveal w));
    intro_exists (G.reveal w) (high_epoch_id_pred (G.reveal init) m b a.high);
    rewrite (ETbl.tperm a.etbl (repr_to_eht_repr m) b
               `star`
             exists_ (high_epoch_id_pred (G.reveal init) m b a.high))
            (get_post init m b a i ret);
    return ret
  end
  else begin
    let x = ETbl.get a.etbl i in
    match x returns ST (get_result v)
                       (ETbl.get_post (repr_to_eht_repr m) b a.etbl i x
                          `star`
                        R.pts_to a.high Steel.FractionalPermission.full_perm (G.reveal w))
                       (get_post init m b a i)
                       (requires ~ (PartialMap.contains i b))
                       (ensures fun res -> Fresh? res ==> Map.sel m i == G.reveal init) with
    | ETbl.Missing j ->
      let ret = NotFound in      
      rewrite (ETbl.get_post (repr_to_eht_repr m) b a.etbl i (ETbl.Missing j))
              (ETbl.tperm a.etbl (repr_to_eht_repr m) b
                 `star`
               pure (ETbl.map_contains_prop j (repr_to_eht_repr m)));
      elim_pure (ETbl.map_contains_prop j (repr_to_eht_repr m));
      intro_pure (high_epoch_id_prop (G.reveal init) m b (G.reveal w));
      intro_exists (G.reveal w) (high_epoch_id_pred (G.reveal init) m b a.high);
      rewrite (ETbl.tperm a.etbl (repr_to_eht_repr m) b
                 `star`
               exists_ (high_epoch_id_pred (G.reveal init) m b a.high))
              (get_post init m b a i ret);
      return ret
    | ETbl.Absent ->
      let ret = NotFound in      
      rewrite (ETbl.get_post (repr_to_eht_repr m) b a.etbl i ETbl.Absent)
              (ETbl.tperm a.etbl (repr_to_eht_repr m) b);
      intro_pure (high_epoch_id_prop (G.reveal init) m b (G.reveal w));
      intro_exists (G.reveal w) (high_epoch_id_pred (G.reveal init) m b a.high);
      rewrite (ETbl.tperm a.etbl (repr_to_eht_repr m) b
                 `star`
               exists_ (high_epoch_id_pred (G.reveal init) m b a.high))
              (get_post init m b a i ret);
      return ret
    | ETbl.Present x ->
      let ret = Found x in
      assert (Some? (PartialMap.sel i (repr_to_eht_repr m)));
      rewrite (ETbl.get_post (repr_to_eht_repr m) b a.etbl i (ETbl.Present x))
              (ETbl.tperm a.etbl (repr_to_eht_repr m) (PartialMap.upd i x b)
                 `star`
               vp i x (Map.sel m i));
      intro_pure (high_epoch_id_prop (G.reveal init) m (PartialMap.upd i x b) (G.reveal w));
      intro_exists (G.reveal w) (high_epoch_id_pred (G.reveal init) m (PartialMap.upd i x b) a.high);
      rewrite (perm a init m (PartialMap.upd i x b)
                 `star`
               vp i x (Map.sel m i))
              (get_post init m b a i ret);
      return ret
  end

let put #v #c #vp #init #m #b a i x content =
  let w = elim_exists () in
  elim_pure (high_epoch_id_prop (G.reveal init) m b (G.reveal w));
  ETbl.put a.etbl i x content;
  assert (PartialMap.equal (PartialMap.upd i (G.reveal content) (repr_to_eht_repr m))
                           (repr_to_eht_repr (Map.upd m i content)));
  rewrite (ETbl.tperm _ _ _)
          (ETbl.tperm a.etbl (repr_to_eht_repr (Map.upd m i content)) (PartialMap.remove i b));
  let high = R.read a.high in
  let r = high `U32.lt` i in
  if r returns STT unit
                   _
                   (fun _ -> perm a init (Map.upd m i content) (PartialMap.remove i b))
  then begin
    R.write a.high i;
    intro_pure (high_epoch_id_prop (G.reveal init) (Map.upd m i content) (PartialMap.remove i b) i);
    intro_exists i (high_epoch_id_pred (G.reveal init) (Map.upd m i content) (PartialMap.remove i b) a.high)
  end
  else begin
    intro_pure (high_epoch_id_prop (G.reveal init) (Map.upd m i content) (PartialMap.remove i b) (G.reveal w));
    intro_exists (G.reveal w) (high_epoch_id_pred (G.reveal init) (Map.upd m i content) (PartialMap.remove i b) a.high)
  end

let ghost_put #_ #v #c #vp #init #m #b a i x content =
  let w = elim_exists () in
  elim_pure (high_epoch_id_prop (G.reveal init) m b (G.reveal w));
  ETbl.ghost_put a.etbl i x content;
  assert (PartialMap.equal (PartialMap.upd i (G.reveal content) (repr_to_eht_repr m))
                           (repr_to_eht_repr (Map.upd m i content)));
  rewrite (ETbl.tperm _ _ _)
          (ETbl.tperm a.etbl (repr_to_eht_repr (Map.upd m i content)) (PartialMap.remove i b));
  intro_pure (high_epoch_id_prop (G.reveal init) (Map.upd m i content) (PartialMap.remove i b) (G.reveal w));
  intro_exists (G.reveal w) (high_epoch_id_pred (G.reveal init) (Map.upd m i content) (PartialMap.remove i b) a.high)

let reclaim #v #c #vp #init #m #b a i =
  let w = elim_exists () in
  elim_pure (high_epoch_id_prop (G.reveal init) m b (G.reveal w));
  let _ = ETbl.remove a.etbl i in
  intro_pure (high_epoch_id_prop (G.reveal init) m (PartialMap.remove i b) (G.reveal w));
  intro_exists (G.reveal w) (high_epoch_id_pred (G.reveal init) m (PartialMap.remove i b) a.high)
