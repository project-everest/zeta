module Zeta.Steel.SafeMain

module Lock = Steel.ST.SpinLock
module R = Steel.ST.Reference

open Steel.ST.GenElim

[@@__reduce__]
let state_ptr_has_core_inv_false
  (p: perm)
: Tot vprop
= pure (p == full_perm)

[@@__reduce__]
let state_ptr_has_core_inv_true
  (state: R.ref M.top_level_state)
: Tot vprop
= exists_ (fun ps -> exists_ (fun ts -> R.pts_to state ps ts `star` M.core_inv ts))

let state_ptr_has_core_inv
  (p: perm)
  (state: R.ref M.top_level_state)
: Tot vprop
= if R.is_null state
  then state_ptr_has_core_inv_false p
  else state_ptr_has_core_inv_true state

[@@__reduce__]
let state_ptr_inv0
  (state_ptr: R.ref (R.ref M.top_level_state))
: Tot vprop
= exists_ (fun (p: perm) -> exists_ (fun (state: R.ref M.top_level_state) ->
    R.pts_to state_ptr p state `star`
    state_ptr_has_core_inv p state
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
    (state_ptr_has_core_inv_false full_perm)
    (state_ptr_has_core_inv full_perm R.null);
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
  (ts: M.top_level_state)
: Tot vprop
= M.core_inv ts `star`
  exists_ (fun p -> exists_ (fun r -> exists_ (fun p0 ->
    R.pts_to handle.state_ptr p r `star`
    R.pts_to r p0 ts
  )))

let handle_pts_to
  (ts: M.top_level_state)
: Tot vprop
= handle_pts_to0 ts

let handle_pts_to_core_inv_intro
  ts
= rewrite (handle_pts_to ts) (handle_pts_to0 ts);
  let _ = gen_elim () in
  M.core_inv_share ts;
  rewrite (handle_pts_to0 ts) (handle_pts_to ts)

let handle_pts_to_core_inv_elim
  ts
= rewrite (handle_pts_to ts) (handle_pts_to0 ts);
  let _ = gen_elim () in
  M.core_inv_gather ts;
  rewrite (handle_pts_to0 ts) (handle_pts_to ts)

let gather ts1 ts2 =
  rewrite (handle_pts_to ts1) (handle_pts_to0 ts1);
  let _ = gen_elim () in
  let pt1 = vpattern_replace (fun pt1 -> R.pts_to handle.state_ptr pt1 _) in
  let p1 = vpattern_replace (fun p1 -> R.pts_to #M.top_level_state _ p1 _) in
  rewrite (handle_pts_to ts2) (handle_pts_to0 ts2);
  let _ = gen_elim () in
  let p2 = vpattern_replace (fun p2 -> R.pts_to #M.top_level_state _ p1 _ `star` R.pts_to #M.top_level_state _ p2 _) in
  R.gather pt1 handle.state_ptr;
  let r = vpattern_replace (R.pts_to handle.state_ptr _) in 
  vpattern_rewrite (fun (r: R.ref M.top_level_state) -> R.pts_to r p1 _) r;
  vpattern_rewrite (fun (r: R.ref M.top_level_state) -> R.pts_to r p2 _) r;
  R.gather p1 r;
  rewrite (M.core_inv ts2) (M.core_inv ts1);
  M.core_inv_gather ts1;
  rewrite (handle_pts_to0 ts1) (handle_pts_to ts1)

let share
  ts
= rewrite (handle_pts_to ts) (handle_pts_to0 ts);
  let _ = gen_elim () in
  let r : R.ref M.top_level_state = vpattern_replace (fun r -> R.pts_to handle.state_ptr _ r `star` R.pts_to r _ ts) in
  R.share handle.state_ptr;
  R.share r;
  M.core_inv_share ts;
  rewrite (handle_pts_to0 ts) (handle_pts_to ts);
  noop ();
  rewrite (handle_pts_to0 ts) (handle_pts_to ts)

#push-options "--z3rlimit 16"
#restart-solver

let init ()
= Lock.acquire handle.lock;
  rewrite (state_ptr_inv handle.state_ptr) (state_ptr_inv0 handle.state_ptr);
  let _ = gen_elim () in
  let state = R.read handle.state_ptr in
  vpattern_rewrite (state_ptr_has_core_inv _) state;
  let p = vpattern_replace (fun p -> state_ptr_has_core_inv p _) in
  if R.is_null state
  then begin
    rewrite (state_ptr_has_core_inv _ _) (state_ptr_has_core_inv_false p);
    let _ = gen_elim () in
    let state = M.init () in
    let ts = elim_exists () in
    M.core_inv_share ts;
    R.pts_to_not_null state;
    vpattern_rewrite (fun p -> R.pts_to handle.state_ptr p _) full_perm;
    R.write handle.state_ptr state;
    R.share handle.state_ptr;
    R.share state;
    rewrite (state_ptr_has_core_inv_true state) (state_ptr_has_core_inv (half_perm full_perm) state);
    rewrite (state_ptr_inv0 handle.state_ptr) (state_ptr_inv handle.state_ptr);
    Lock.release handle.lock;
    rewrite (handle_pts_to0 ts) (handle_pts_to ts);
    rewrite (init_post_true ts) (init_post true ts);
    return true
  end else begin
    rewrite (state_ptr_has_core_inv _ _) (state_ptr_has_core_inv_true state);
    let _ = gen_elim () in
    let ts = vpattern_replace_erased (fun ts -> R.pts_to state _ ts `star` M.core_inv ts) in
    R.share state;
    M.core_inv_share ts;
    rewrite (R.pts_to handle.state_ptr _ _) (R.pts_to handle.state_ptr p state);
    R.share handle.state_ptr;
    rewrite (state_ptr_has_core_inv_true state) (state_ptr_has_core_inv (half_perm p) state);
    rewrite (state_ptr_inv0 handle.state_ptr) (state_ptr_inv handle.state_ptr);
    Lock.release handle.lock;
    rewrite (handle_pts_to0 ts) (handle_pts_to ts);
    rewrite emp (init_post false ts);
    return false
  end

#pop-options

let verify_log
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
    (handle_pts_to t `star`
     A.pts_to input log_perm log_bytes `star`
     A.pts_to output full_perm out_bytes `star`
     M.log_of_tid t tid entries)
    (fun res ->
       handle_pts_to t `star`
       M.verify_post t tid entries log_perm log_bytes len input out_len out_bytes output res)
= rewrite (handle_pts_to t) (handle_pts_to0 t);
  let _ = gen_elim () in
  let state = R.read handle.state_ptr in
  vpattern_rewrite (R.pts_to handle.state_ptr _) state;
  vpattern_rewrite (fun (state: R.ref M.top_level_state) -> R.pts_to state _ t) state;
  M.core_inv_share t;
  let res = M.verify_log state tid len input out_len output in
  rewrite (handle_pts_to0 t) (handle_pts_to t);
  return res

let max_certified_epoch
                        (#t:Ghost.erased M.top_level_state)
                        (_: unit)
  : STT AEH.max_certified_epoch_result
        (handle_pts_to t)
        (fun res ->
           handle_pts_to t `star`
           M.read_max_post t res)
=
  rewrite (handle_pts_to t) (handle_pts_to0 t);
  let _ = gen_elim () in
  let state = R.read handle.state_ptr in
  vpattern_rewrite (R.pts_to handle.state_ptr _) state;
  vpattern_rewrite (fun (state: R.ref M.top_level_state) -> R.pts_to state _ t) state;
  let res = M.max_certified_epoch state in
  rewrite (handle_pts_to0 t) (handle_pts_to t);
  return res
