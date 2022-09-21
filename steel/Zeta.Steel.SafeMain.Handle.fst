module Zeta.Steel.SafeMain.Handle

module M = Zeta.Steel.Main
module AEH = Zeta.Steel.AggregateEpochHashes
module AT = Zeta.Steel.ApplicationTypes
module U16 = FStar.UInt16
module U32 = FStar.UInt32

module Lock = Steel.ST.SpinLock
module R = Steel.ST.Reference
module A = Steel.ST.Array

open Steel.ST.GenElim

noeq
type state_t = {
  state: R.ref (M.top_level_state false);
  tl_state: Ghost.erased (M.top_level_state false);
}

[@@__reduce__]
let handle_pts_to_body0
  (r2: state_t)
: Tot vprop
= exists_ (fun p3 ->
    R.pts_to r2.state p3 r2.tl_state `star`
    M.core_inv r2.tl_state
  )

let handle_pts_to_body
  (r2: state_t)
: Tot vprop
= handle_pts_to_body0 r2

let gather_body
  (#opened: _)
  (r2: state_t)
: STGhostT unit opened
    (handle_pts_to_body r2 `star` handle_pts_to_body r2)
    (fun _ -> handle_pts_to_body r2)
= rewrite (handle_pts_to_body r2) (handle_pts_to_body0 r2);
  let _ = gen_elim () in
  let ps = vpattern_replace (fun ps -> R.pts_to r2.state ps _) in
  rewrite (handle_pts_to_body r2) (handle_pts_to_body0 r2);
  let _ = gen_elim () in
  R.gather ps r2.state;
  M.core_inv_gather _;
  rewrite (handle_pts_to_body0 r2) (handle_pts_to_body r2)

let share_body
  (#opened: _)
  (r2: state_t)
: STGhostT unit opened
    (handle_pts_to_body r2)
    (fun _ -> handle_pts_to_body r2 `star` handle_pts_to_body r2)
= rewrite (handle_pts_to_body r2) (handle_pts_to_body0 r2);
  let _ = gen_elim () in
  R.share r2.state;
  M.core_inv_share _;
  rewrite (handle_pts_to_body0 r2) (handle_pts_to_body r2);
  noop ();
  rewrite (handle_pts_to_body0 r2) (handle_pts_to_body r2)

noeq
type handle_t = {
  state: state_t;
  _inv: inv (handle_pts_to_body state);
}

let handle: handle_t =
  begin
    let r2_state = M.init false in
    let ts = elim_exists () in
    rewrite (M.init_post _) emp;
    [@@inline_let]
    let r2 : state_t = ({
      state = r2_state;
      tl_state = ts;
    })
    in
    rewrite (R.pts_to r2_state full_perm _) (R.pts_to r2.state full_perm r2.tl_state);
    vpattern_rewrite M.core_inv (Ghost.reveal r2.tl_state);
    rewrite (handle_pts_to_body0 r2) (handle_pts_to_body r2);
    let i = new_invariant (handle_pts_to_body r2) in
    return ({
      state = r2;
      _inv = i;
    })
  end <: STT handle_t emp (fun _ -> emp)
