module Zeta.Steel.SafeMain

module Lock = Steel.ST.SpinLock
module R = Steel.ST.Reference

open Steel.ST.GenElim

let state_ptr_inv_prop
  (p: perm)
  (state: R.ref M.top_level_state)
: Tot prop
= R.is_null state ==> p == full_perm

[@@__reduce__]
let state_ptr_inv0
  (state_ptr: R.ref (R.ref M.top_level_state))
: Tot vprop
= exists_ (fun (p: perm) -> exists_ (fun (state: R.ref M.top_level_state) ->
    R.pts_to state_ptr p state `star`
    pure (state_ptr_inv_prop p state)
  ))

let state_ptr_inv
  (state_ptr: R.ref (R.ref M.top_level_state))
: Tot vprop
= state_ptr_inv0 state_ptr

noeq
type handle_t = {
  state_ptr: R.ref (R.ref M.top_level_state);
  lock: Lock.lock (state_ptr_inv state_ptr);
}

let create_handle () : STT handle_t emp (fun _ -> emp) =
  let state_ptr : R.ref (R.ref M.top_level_state) = R.alloc R.null in
  noop ();
  rewrite
    (state_ptr_inv0 state_ptr)
    (state_ptr_inv state_ptr);
  let lock = Lock.new_lock (state_ptr_inv state_ptr) in
  return ({
    state_ptr = state_ptr;
    lock = lock;
  })

(* FIXME: this makes F* crash with
(Error) ASSERTION FAILURE: Impossible! check_top_level_let: got unexpected effect args
F* may be in an inconsistent state.
Please file a bug report, ideally with a minimized version of the program that triggered the error.

let handle = create_handle () 
*)

assume val handle: handle_t

[@@__reduce__]
let handle_pts_to0
  (p0: perm)
  (ts: M.top_level_state)
: Tot vprop
= exists_ (fun p -> exists_ (fun r ->
    R.pts_to handle.state_ptr p r `star`
    R.pts_to r p0 ts
  ))

let handle_pts_to
  (p: perm)
  (ts: M.top_level_state)
: Tot vprop
= handle_pts_to0 p ts

let gather p1 ts1 p2 ts2 =
  rewrite (handle_pts_to p1 ts1) (handle_pts_to0 p1 ts1);
  let _ = gen_elim () in
  let pt1 = vpattern_replace (fun pt1 -> R.pts_to handle.state_ptr pt1 _) in
  rewrite (handle_pts_to p2 ts2) (handle_pts_to0 p2 ts2);
  let _ = gen_elim () in
  R.gather pt1 handle.state_ptr;
  let r = vpattern_replace (R.pts_to handle.state_ptr _) in 
  vpattern_rewrite (fun (r: R.ref M.top_level_state) -> R.pts_to r p1 _) r;
  vpattern_rewrite (fun (r: R.ref M.top_level_state) -> R.pts_to r p2 _) r;
  R.gather _ r;
  rewrite (handle_pts_to0 (p1 `sum_perm` p2) ts1) (handle_pts_to (p1 `sum_perm` p2) ts1)

let share
  p ts
= rewrite (handle_pts_to p ts) (handle_pts_to0 p ts);
  let _ = gen_elim () in
  let r : R.ref M.top_level_state = vpattern_replace (fun r -> R.pts_to handle.state_ptr _ r `star` R.pts_to r p ts) in
  R.share handle.state_ptr;
  R.share r;
  rewrite (handle_pts_to0 (half_perm p) ts) (handle_pts_to (half_perm p) ts);
  noop ();
  rewrite (handle_pts_to0 (half_perm p) ts) (handle_pts_to (half_perm p) ts)

#push-options "--z3rlimit 16"
#restart-solver

let init () : STT bool
  emp
  (fun b -> init_post b)
= Lock.acquire handle.lock;
  rewrite (state_ptr_inv handle.state_ptr) (state_ptr_inv0 handle.state_ptr);
  let _ = gen_elim () in
  let state = R.read handle.state_ptr in
  if R.is_null state
  then begin
    let state = M.init () in
    let ts = elim_exists () in
    R.pts_to_not_null state;
    assert (state_ptr_inv_prop (half_perm full_perm) state);
    vpattern_rewrite (fun p -> R.pts_to handle.state_ptr p _) full_perm;
    R.write handle.state_ptr state;
    R.share handle.state_ptr;
    rewrite (state_ptr_inv0 handle.state_ptr) (state_ptr_inv handle.state_ptr);
    Lock.release handle.lock;
    rewrite (handle_pts_to0 full_perm ts) (handle_pts_to full_perm ts);
    rewrite init_post_true (init_post true);
    return true
  end else begin
    noop ();
    rewrite (state_ptr_inv0 handle.state_ptr) (state_ptr_inv handle.state_ptr);
    Lock.release handle.lock;
    rewrite emp (init_post false);
    return false
  end

#pop-options

let verify_log (#p: perm)
               (#t:Ghost.erased M.top_level_state)
               (tid:_)
               (#entries:Ghost.erased AEH.log)
               (#log_perm:perm)
               (#log_bytes:Ghost.erased AT.bytes)
               (len: U32.t { len <> 0ul })
               (input:U.larray U8.t len)
               (out_len: U32.t)
               (#out_bytes:Ghost.erased AT.bytes)
               (output:U.larray U8.t out_len)
  : STT (option (v:V.verify_result { V.verify_result_complete len v }))
    (handle_pts_to p t `star`
     M.core_inv t `star`
     A.pts_to input log_perm log_bytes `star`
     A.pts_to output full_perm out_bytes `star`
     M.log_of_tid t tid entries)
    (fun res ->
       handle_pts_to p t `star`
       M.verify_post t tid entries log_perm log_bytes len input out_len out_bytes output res)
= rewrite (handle_pts_to p t) (handle_pts_to0 p t);
  let _ = gen_elim () in
  let state = R.read handle.state_ptr in
  vpattern_rewrite (R.pts_to handle.state_ptr _) state;
  vpattern_rewrite (fun (state: R.ref M.top_level_state) -> R.pts_to state p t) state;
  let res = M.verify_log state tid len input out_len output in
  rewrite (handle_pts_to0 p t) (handle_pts_to p t);
  return res

let max_certified_epoch (#p: perm)
                        (#t:Ghost.erased M.top_level_state)
                        (_: unit)
  : STT AEH.max_certified_epoch_result
        (handle_pts_to p t)
        (fun res ->
           handle_pts_to p t `star`
           M.read_max_post t res)
=
  rewrite (handle_pts_to p t) (handle_pts_to0 p t);
  let _ = gen_elim () in
  let state = R.read handle.state_ptr in
  vpattern_rewrite (R.pts_to handle.state_ptr _) state;
  vpattern_rewrite (fun (state: R.ref M.top_level_state) -> R.pts_to state p t) state;
  let res = M.max_certified_epoch state in
  rewrite (handle_pts_to0 p t) (handle_pts_to p t);
  return res
