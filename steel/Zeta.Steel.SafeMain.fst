module Zeta.Steel.SafeMain

module Lock = Steel.ST.SpinLock
module R = Steel.ST.Reference

open Steel.ST.GenElim

[@@__reduce__]
let state_ptr_inv_null
  (p: perm)
: Tot vprop
= pure (p == full_perm)

[@@__reduce__]
let state_ptr_inv_not_null
  (state: R.ref M.top_level_state)
: Tot vprop
= exists_ (fun pt -> exists_ (fun t -> R.pts_to state pt t `star` M.core_inv t))

let state_ptr_inv_if
  (state: R.ref M.top_level_state)
  (p: perm)
: Tot vprop
= if R.is_null state
  then state_ptr_inv_null p
  else state_ptr_inv_not_null state

[@@__reduce__]
let state_ptr_inv0
  (state_ptr: R.ref (R.ref M.top_level_state))
: Tot vprop
= exists_ (fun p -> exists_ (fun state ->
    R.pts_to state_ptr (half_perm p) state `star`
    state_ptr_inv_if state p
  ))

let state_ptr_inv
  (state_ptr: R.ref (R.ref M.top_level_state))
: Tot vprop
= state_ptr_inv0 state_ptr

let state_ptr_lock_prop
  (state: R.ref M.top_level_state)
  (p: perm)
: Tot prop
= R.is_null state == true ==> p == full_perm

[@@__reduce__]
let state_ptr_lock0
  (state_ptr: R.ref (R.ref M.top_level_state))
: Tot vprop
= exists_ (fun p -> exists_ (fun state ->
    R.pts_to state_ptr (half_perm p) state `star`
    pure (state_ptr_lock_prop state p)
  ))

let state_ptr_lock
  (state_ptr: R.ref (R.ref M.top_level_state))
: Tot vprop
= state_ptr_lock0 state_ptr

noeq
type handle_t = {
  state_ptr: R.ref (R.ref M.top_level_state);
  _inv: inv (state_ptr_inv state_ptr);
  _lock: Lock.lock (state_ptr_lock state_ptr);
}

let create_handle () : STT handle_t emp (fun _ -> emp) =
  let state_ptr : R.ref (R.ref M.top_level_state) = R.alloc R.null in
  R.share state_ptr;
  (* invariant *)
  rewrite (state_ptr_inv_null full_perm) (state_ptr_inv_if R.null full_perm);
  rewrite (state_ptr_inv0 state_ptr) (state_ptr_inv state_ptr);
  let _inv = new_invariant (state_ptr_inv state_ptr) in
  (* lock *)
  rewrite (state_ptr_lock0 state_ptr) (state_ptr_lock state_ptr);
  let _lock = Lock.new_lock (state_ptr_lock state_ptr) in
  (* summary *)
  return ({
    state_ptr = state_ptr;
    _inv = _inv;
    _lock = _lock;
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

let with_invariant_g (#a:Type)
                     (#fp:vprop)
                     (#fp':a -> vprop)
                     (#opened_invariants:inames)
                     (#p:vprop)
                     (i:inv p{not (mem_inv opened_invariants i)})
                     (f:unit -> STGhostT a (add_inv opened_invariants i)
                                         (p `star` fp)
                                         (fun x -> p `star` fp' x))
  : STGhostT a opened_invariants fp fp'
= with_invariant_g i f

let gen_handle_pts_to_not_null
  (#opened: _)
  (#p: _)
  (#state: _)
  ()
: STGhost (Ghost.erased M.top_level_state) opened
    (R.pts_to handle.state_ptr p state)
    (fun ts -> exists_ (fun p' -> R.pts_to handle.state_ptr (half_perm p') state) `star` handle_pts_to ts)
    ((not (mem_inv opened handle._inv)) /\
      (not (R.is_null state))
    )
    (fun _ -> True)
= noop (); // for pure
  with_invariant_g
    #(Ghost.erased M.top_level_state)
    #(R.pts_to handle.state_ptr p state `star` pure (R.is_null state == false))
    #(fun ts -> (exists_ (fun p' -> R.pts_to handle.state_ptr (half_perm p') state) `star` handle_pts_to ts))
    #opened
    #(state_ptr_inv handle.state_ptr)
    handle._inv
    (fun _ ->
      rewrite
        (state_ptr_inv handle.state_ptr)
        (state_ptr_inv0 handle.state_ptr);
      let _ = gen_elim () in
      R.gather p handle.state_ptr;
      vpattern_rewrite (R.pts_to handle.state_ptr _) state;
      rewrite
        (state_ptr_inv_if _ _)
        (state_ptr_inv_not_null state);
      let _ = gen_elim () in
      let ts = vpattern_replace_erased (fun ts -> R.pts_to state _ ts `star` M.core_inv ts) in
      R.share state;
      M.core_inv_share ts;
      R.share handle.state_ptr;
      (* handle_pts_to *)
      rewrite (handle_pts_to0 ts) (handle_pts_to ts);
      let p' = vpattern_replace (fun p' -> R.pts_to handle.state_ptr p' _) in
      R.share handle.state_ptr;
      (* invariant *)
      rewrite
        (state_ptr_inv_not_null state)
        (state_ptr_inv_if state p');
      rewrite
        (state_ptr_inv0 handle.state_ptr)
        (state_ptr_inv handle.state_ptr);
      (* postcond *)
      noop ();
      ts
    )

assume
val atomic_read_ref
  (#t: Type)
  (#opened:_)
  (#p:perm)
  (#v:Ghost.erased t)
  (r:R.ref t)
  : STAtomic t opened
      (R.pts_to r p v)
      (fun x -> R.pts_to r p v)
      (requires True)
      (ensures fun x -> x == Ghost.reveal v)

assume
val atomic_write_ref
  (#t: Type)
  (#opened:_)
  (#v:Ghost.erased t)
  (r:R.ref t)
  (x:t)
  : STAtomicT unit opened
      (R.pts_to r full_perm v)
      (fun _ -> R.pts_to r full_perm x)

let handle_is_null_post (b: bool) : vprop =
  if b
  then emp
  else exists_ handle_pts_to

inline_for_extraction
let with_invariant (#a:Type)
                   (#fp:vprop)
                   (#fp':a -> vprop)
                   (#opened_invariants:inames)
                   (#p:vprop)
                   (i:inv p{not (mem_inv opened_invariants i)})
                   (f:unit -> STAtomicT a (add_inv opened_invariants i)
                                          (p `star` fp)
                                          (fun x -> p `star` fp' x))
  : STAtomicT a opened_invariants fp fp'
= with_invariant i f

let handle_is_null
  (#opened: _)
  ()
: STAtomic bool opened
    emp
    (fun b -> handle_is_null_post b)
    (not (mem_inv opened handle._inv))
    (fun _ -> True)
= noop (); // for pure
  with_invariant
    #bool
    #emp
    #(fun b -> handle_is_null_post b)
    #_
    #(state_ptr_inv handle.state_ptr)
    handle._inv
    (fun _ ->
      rewrite
        (state_ptr_inv handle.state_ptr)
        (state_ptr_inv0 handle.state_ptr);
      let _ = gen_elim () in
      let state = atomic_read_ref handle.state_ptr in
      if R.is_null state
      then begin
        noop ();
        rewrite
          (state_ptr_inv0 handle.state_ptr)
          (state_ptr_inv handle.state_ptr);
        rewrite
          emp
          (handle_is_null_post true);
        return true
      end else begin
        let p = vpattern_replace (fun p -> R.pts_to handle.state_ptr (half_perm p) _ `star` state_ptr_inv_if _ p) in
        let state = vpattern_replace_erased (fun state -> R.pts_to handle.state_ptr _ state `star` state_ptr_inv_if state _) in
        rewrite
          (state_ptr_inv_if _ _)
          (state_ptr_inv_not_null state);
        let _ = gen_elim () in
        R.share handle.state_ptr;
        R.share state;
        M.core_inv_share _;
        (* invariant *)
        rewrite
          (state_ptr_inv_not_null state)
          (state_ptr_inv_if state (half_perm p));
        rewrite
          (state_ptr_inv0 handle.state_ptr)
          (state_ptr_inv handle.state_ptr);
        (* handle_pts_to *)
        let ts = vpattern_replace_erased (fun ts -> R.pts_to state _ ts `star` M.core_inv ts) in
        rewrite
          (handle_pts_to0 ts)
          (handle_pts_to ts);
        rewrite 
          (exists_ handle_pts_to)
          (handle_is_null_post false);
        return false
      end
    )

#push-options "--z3rlimit 32"
#restart-solver

let init ()
= Lock.acquire handle._lock;
  rewrite (state_ptr_lock handle.state_ptr) (state_ptr_lock0 handle.state_ptr);
  let _ = gen_elim () in
  let state = R.read handle.state_ptr in
  if R.is_null state
  then begin
    let state' = M.init () in
    let ts = elim_exists () in
    R.pts_to_not_null state';
    rewrite (R.pts_to handle.state_ptr _ _) (R.pts_to handle.state_ptr (half_perm full_perm) state);
    M.core_inv_share ts;
    R.share state';
    with_invariant
      #unit
      #(R.pts_to handle.state_ptr (half_perm full_perm) state `star` R.pts_to state' (half_perm full_perm) ts `star` M.core_inv ts)
      #(fun _ -> R.pts_to handle.state_ptr (half_perm full_perm) state')
      #_
      #(state_ptr_inv handle.state_ptr)
      (handle._inv)
      (fun _ ->
        rewrite (state_ptr_inv handle.state_ptr) (state_ptr_inv0 handle.state_ptr);
        let _ = gen_elim () in
        R.gather (half_perm full_perm) handle.state_ptr;
        let p = vpattern_replace (state_ptr_inv_if _) in
        rewrite
          (state_ptr_inv_if _ _)
          (state_ptr_inv_null p);
        let _ = gen_elim () in
        vpattern_rewrite (fun p -> R.pts_to handle.state_ptr p _) full_perm;
        atomic_write_ref handle.state_ptr state';
        R.share handle.state_ptr;
        noop ();
        rewrite
          (state_ptr_inv_not_null state')
          (state_ptr_inv_if state' full_perm);
        rewrite
          (state_ptr_inv0 handle.state_ptr)
          (state_ptr_inv handle.state_ptr)
      );
    R.share handle.state_ptr;
    rewrite (state_ptr_lock0 handle.state_ptr) (state_ptr_lock handle.state_ptr);
    Lock.release handle._lock;
    rewrite (handle_pts_to0 ts) (handle_pts_to ts);
    rewrite (init_post_true ts) (init_post true ts);
    return true
  end else begin
    let ts = gen_handle_pts_to_not_null () in
    let _ = gen_elim () in
    rewrite (state_ptr_lock0 handle.state_ptr) (state_ptr_lock handle.state_ptr);
    Lock.release handle._lock;
    rewrite emp (init_post false ts);
    return false
  end

#pop-options

assume val acquire_thread_lock
  (t: Ghost.erased M.top_level_state)
  (tid: AT.tid)
: STT (Ghost.erased AEH.log)
    (handle_pts_to t)
    (fun entries -> handle_pts_to t `star` M.log_of_tid t tid entries)

assume val release_thread_lock
  (t: Ghost.erased (M.top_level_state))
  (tid: AT.tid)
  (entries: Ghost.erased AEH.log)
: STT unit
    (handle_pts_to t `star` M.log_of_tid t tid entries)
    (fun _ -> handle_pts_to t)

#push-options "--z3rlimit 32 --query_stats --ifuel 6"
#restart-solver

let m_verify_post_failure_eq
  (#opened: _)
  (t:M.top_level_state)
  (tid:AT.tid)
  (entries:Ghost.erased AEH.log)
  (log_perm:perm)
  (log_bytes:Ghost.erased AT.bytes)
  (len: U32.t)
  (input:U.larray U8.t len)
  (out_len: U32.t)
  (out_bytes:Ghost.erased AT.bytes)
  (output:U.larray U8.t out_len)
  (res: (option (v:V.verify_result { V.verify_result_complete len v })))
: STGhost unit opened
  (
    M.verify_post t tid entries log_perm log_bytes len input out_len out_bytes output res
  )
  (fun _ ->
    M.core_inv t `star`
    A.pts_to input log_perm log_bytes `star` (
       exists_ (fun s -> A.pts_to output full_perm s) `star`
       exists_ (fun entries' -> M.log_of_tid t tid entries'))
  )
  (match res with
  | Some (V.Verify_success _ _) -> False
  | _ -> True
  )
  (fun _ -> True)
= rewrite
    (M.verify_post t tid entries log_perm log_bytes len input out_len out_bytes output res)
    (M.core_inv t `star`
    A.pts_to input log_perm log_bytes `star` (
       exists_ (fun s -> A.pts_to output full_perm s) `star`
       exists_ (fun entries' -> M.log_of_tid t tid entries')))

let verify_log_some
               (t: Ghost.erased M.top_level_state)
               (tid:U16.t)
               (#log_perm:perm)
               (#log_bytes:Ghost.erased AT.bytes)
               (len: U32.t)
               (input: EXT.extern_ptr U8.t)
               (out_len: U32.t)
               (#out_bytes:Ghost.erased AT.bytes)
               (output: EXT.extern_ptr U8.t)
  : ST (verify_result len)
    (handle_pts_to t `star` verify_pre log_perm log_bytes input out_bytes output)
    (fun res -> verify_post tid log_perm log_bytes len input out_len out_bytes output res)
    (check_verify_input tid len input out_len output)
    (fun _ -> True)
= let entries = acquire_thread_lock t tid in
  rewrite (handle_pts_to t) (handle_pts_to0 t);
  let _ = gen_elim () in
  let state = R.read handle.state_ptr in
  vpattern_rewrite (R.pts_to handle.state_ptr _) state;
  vpattern_rewrite (fun (state: R.ref M.top_level_state) -> R.pts_to state _ t) state;
  let input' = EXT.take input len in
  let output' = EXT.take output out_len in
  vpattern_rewrite (fun a -> A.pts_to a log_perm log_bytes) input';
  vpattern_rewrite (fun a -> A.pts_to a full_perm out_bytes) output';
  let v = M.verify_log state tid len input' out_len output' in
  let res = Some v in
  match v returns STT (verify_result len) (R.pts_to handle.state_ptr _ _ `star` R.pts_to state _ _ `star`  M.verify_post t tid entries log_perm log_bytes len input' out_len out_bytes output' v) (fun res -> verify_post tid log_perm log_bytes len input out_len out_bytes output res) with
  | Some (V.Verify_success read wrote) ->
    rewrite
      (M.verify_post t tid entries log_perm log_bytes len input' out_len out_bytes output' _)
      (M.core_inv t `star`
        A.pts_to (EXT.gtake input) log_perm log_bytes `star`
        exists_ (M.verify_post_success_pred t tid entries log_bytes out_len out_bytes output' read wrote)
      );
    let _ = gen_elim () in
    rewrite (handle_pts_to0 t) (handle_pts_to t);
    let entries' = vpattern_erased (fun entries' -> M.log_of_tid t tid (_ `Seq.append` entries')) in
    let out_bytes' = vpattern_replace_erased (A.pts_to output' _) in
    release_thread_lock t tid _;
    vpattern_rewrite #_ #_ #output' (fun output -> A.pts_to output _ _) (EXT.gtake output);
    assert_ (verify_post_some_m_success_body tid log_perm log_bytes len input out_len out_bytes output v () t entries read wrote entries' out_bytes');
    rewrite
      (verify_post_some_m_success tid log_perm log_bytes len input out_len out_bytes output v () t entries read wrote)
      (verify_post_some_m tid log_perm log_bytes len input out_len out_bytes output v () t entries);
    rewrite
      (verify_post_some tid log_perm log_bytes len input out_len out_bytes output v ())
      (verify_post tid log_perm log_bytes len input out_len out_bytes output res);
    return res
  | v ->
    m_verify_post_failure_eq t tid entries log_perm log_bytes len input' out_len out_bytes output' v;
    let _ = gen_elim () in
    rewrite (handle_pts_to0 t) (handle_pts_to t);
    release_thread_lock t tid _;
    vpattern_rewrite #_ #_ #output' (fun output -> A.pts_to output _ _) (EXT.gtake output);
    rewrite
      (verify_post_some_m_failure output)
      (verify_post_some_m tid log_perm log_bytes len input out_len out_bytes output v () t entries);
    vpattern_rewrite #_ #_ #input' (fun input -> A.pts_to input _ _) (EXT.gtake input);
    rewrite
      (verify_post_some tid log_perm log_bytes len input out_len out_bytes output v ())
      (verify_post tid log_perm log_bytes len input out_len out_bytes output res);
    return res

let verify_log
  tid #log_perm #log_bytes len input out_len #out_bytes output
=
  if not (check_verify_input tid len input out_len output) returns STT (verify_result len)
    (verify_pre log_perm log_bytes input out_bytes output)
    (fun res -> verify_post tid log_perm log_bytes len input out_len out_bytes output res)
  then begin
    noop ();
    rewrite (verify_pre log_perm log_bytes input out_bytes output)
      (verify_post tid log_perm log_bytes len input out_len out_bytes output None);
    return None
  end else
  let is_null = handle_is_null () in
  if is_null
  then begin
    noop ();
    rewrite (handle_is_null_post _) emp;
    rewrite (verify_pre log_perm log_bytes input out_bytes output)
      (verify_post tid log_perm log_bytes len input out_len out_bytes output None);
    return None
  end else 
  begin
    noop ();
    rewrite (handle_is_null_post _) (exists_ handle_pts_to);
    let ts = elim_exists () in
    verify_log_some ts tid len input out_len output
  end

let max_certified_epoch
  ()
=
  let is_null = handle_is_null () in
  if is_null
  then begin
    noop ();
    rewrite (handle_is_null_post _) (max_certified_epoch_post None);
    return None
  end else 
  begin
    noop ();
    rewrite (handle_is_null_post _) (exists_ handle_pts_to);
    let t = elim_exists () in
    rewrite (handle_pts_to t) (handle_pts_to0 t);
    let _ = gen_elim () in
    let state = R.read handle.state_ptr in
    vpattern_rewrite (R.pts_to handle.state_ptr _) state;
    vpattern_rewrite (fun (state: R.ref M.top_level_state) -> R.pts_to state _ t) state;
    let r = M.max_certified_epoch state in
    rewrite (handle_pts_to0 t) (handle_pts_to t);
    let res = Some r in
    rewrite (max_certified_epoch_post_some r) (max_certified_epoch_post res);
    return res
  end

#pop-options
