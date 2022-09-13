module Zeta.Steel.SafeMain

module Lock = Steel.ST.SpinLock
module R = Steel.ST.Reference

open Steel.ST.GenElim

// TODO: use FStarLang/FStar#2349 to nest structs and take pointers to fields. However, we need support for atomic accesses for such references, at least for the top-level cases (so far we don't need atomic field accesses here yet)

[@@__reduce__]
let thread_lock_vprop
  (tl_state: M.top_level_state)
  (tid: AT.tid)
: Tot vprop
= exists_ (fun (entries: AEH.log) -> M.log_of_tid tl_state tid entries)

let thread_lock_t
  (tl_state: M.top_level_state)
: Tot Type
= (tid: Ghost.erased AT.tid & Lock.lock (thread_lock_vprop tl_state tid))

let thread_state_prop
  (#tl_state: M.top_level_state)
  (a: Seq.seq (thread_lock_t tl_state))
: Tot prop
= forall (i: nat { i < Seq.length a }) . {:pattern (Seq.index a i)} U16.v (dfst (Seq.index a i)) == i

noeq
type state_t = {
  state: R.ref M.top_level_state;
  tl_state: Ghost.erased M.top_level_state;
  thread_locks: A.array (thread_lock_t tl_state);
  tl_thread_locks: Ghost.erased (Seq.seq (thread_lock_t tl_state));
  tl_frozen_logs: Ghost.erased M.tid_log_map;
  tl_prf: squash (thread_state_prop tl_thread_locks /\ Seq.length tl_thread_locks == U32.v AT.n_threads);
}

[@@__reduce__]
let state_ptr_inv_null
  (p: perm)
: Tot vprop
= pure (p == full_perm)

[@@__reduce__]
let handle_pts_to_body0
  (r2: state_t)
: Tot vprop
= exists_ (fun p3 -> exists_ (fun p4 ->
    R.pts_to r2.state p3 r2.tl_state `star`
    A.pts_to r2.thread_locks p4 r2.tl_thread_locks `star`
    M.core_inv r2.tl_state `star`
    M.frozen_logs r2.tl_state r2.tl_frozen_logs
  ))

let handle_pts_to_body
  (r2: state_t)
: Tot vprop
= handle_pts_to_body0 r2

[@@__reduce__]
let state_ptr_inv_not_null_body
  (state: R.ref state_t)
  (st: state_t)
: Tot vprop
= exists_ (fun p1 ->
    R.pts_to state p1 st `star`
    handle_pts_to_body st
  )

[@@__reduce__]
let state_ptr_inv_not_null
  (state: R.ref state_t)
: Tot vprop
= exists_ (fun st ->
    state_ptr_inv_not_null_body state st
  )

let state_ptr_inv_if
  (state: R.ref state_t)
  (p: perm)
: Tot vprop
= if R.is_null state
  then state_ptr_inv_null p
  else state_ptr_inv_not_null state

[@@__reduce__]
let state_ptr_inv0
  (state_ptr: R.ref (R.ref state_t))
: Tot vprop
= exists_ (fun p -> exists_ (fun state ->
    R.pts_to state_ptr (half_perm p) state `star`
    state_ptr_inv_if state p
  ))

let state_ptr_inv
  (state_ptr: R.ref (R.ref state_t))
: Tot vprop
= state_ptr_inv0 state_ptr

let state_ptr_lock_prop
  (state: R.ref state_t)
  (p: perm)
: Tot prop
= R.is_null state == true ==> p == full_perm

[@@__reduce__]
let state_ptr_lock0
  (state_ptr: R.ref (R.ref state_t))
: Tot vprop
= exists_ (fun p -> exists_ (fun state ->
    R.pts_to state_ptr (half_perm p) state `star`
    pure (state_ptr_lock_prop state p)
  ))

let state_ptr_lock
  (state_ptr: R.ref (R.ref state_t))
: Tot vprop
= state_ptr_lock0 state_ptr

noeq
type handle_t = {
  state_ptr: R.ref (R.ref state_t);
  _inv: inv (state_ptr_inv state_ptr);
  _lock: Lock.lock (state_ptr_lock state_ptr);
}

let create_handle () : STT handle_t emp (fun _ -> emp) =
  let state_ptr : R.ref (R.ref state_t) = R.alloc R.null in
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
let handle_pts_to_aux0
  (r2: state_t)
: Tot vprop
= exists_ (fun p1 -> exists_ (fun r1 ->
    R.pts_to handle.state_ptr p1 r1 `star`
    state_ptr_inv_not_null_body r1 r2
  ))

let handle_pts_to_aux
  (r2: state_t)
: Tot vprop
= handle_pts_to_aux0 r2

[@@__reduce__]
let handle_pts_to0
  (ts: M.top_level_state)
: Tot vprop
= exists_ (fun r2 ->
    handle_pts_to_aux r2 `star`
    pure (ts == Ghost.reveal r2.tl_state)
  )

let handle_pts_to
  (ts: M.top_level_state)
: Tot vprop
= handle_pts_to0 ts

let gather_body
  (#opened: _)
  (r2: state_t)
: STGhostT unit opened
    (handle_pts_to_body r2 `star` handle_pts_to_body r2)
    (fun _ -> handle_pts_to_body r2)
= rewrite (handle_pts_to_body r2) (handle_pts_to_body0 r2);
  let _ = gen_elim () in
  let ps = vpattern_replace (fun ps -> R.pts_to r2.state ps _) in
  let pa = vpattern_replace (fun pa -> A.pts_to r2.thread_locks pa _) in
  rewrite (handle_pts_to_body r2) (handle_pts_to_body0 r2);
  let _ = gen_elim () in
  A.gather r2.thread_locks pa _;
  R.gather ps r2.state;
  M.core_inv_gather _;
  M.frozen_logs_gather _ _;
  rewrite (handle_pts_to_body0 r2) (handle_pts_to_body r2)

let gather_aux
  (#opened: _)
  (ts1: state_t)
  (ts2: state_t)
: STGhost unit opened
    (handle_pts_to_aux ts1 `star` handle_pts_to_aux ts2)
    (fun _ -> handle_pts_to_aux ts1)
    True
    (fun _ -> ts1 == ts2)
= rewrite (handle_pts_to_aux ts1) (handle_pts_to_aux0 ts1);
  let _ = gen_elim () in
  let r1 = vpattern_replace (fun r1 -> R.pts_to handle.state_ptr _ r1 `star` R.pts_to r1 _ _) in
  rewrite (handle_pts_to_aux ts2) (handle_pts_to_aux0 ts2);
  let _ = gen_elim () in
  let r2 = vpattern_replace (fun r2 -> R.pts_to handle.state_ptr _ r1 `star` R.pts_to handle.state_ptr _ r2 `star` R.pts_to r2 _ _) in
  R.gather _ #r1 handle.state_ptr;
  vpattern_rewrite #_ #_ #r2 (fun r2 -> R.pts_to r2 _ _) r1;
  R.gather _ #ts1 r1;
  rewrite (handle_pts_to_body ts2) (handle_pts_to_body ts1);
  gather_body ts1;
  rewrite (handle_pts_to_aux0 ts1) (handle_pts_to_aux ts1)
  
let gather ts ts' =
  rewrite (handle_pts_to ts) (handle_pts_to0 ts);
  let _ = gen_elim () in
  let ts1 = vpattern_replace handle_pts_to_aux in
  rewrite (handle_pts_to ts') (handle_pts_to0 ts');
  let _ = gen_elim () in
  gather_aux ts1 _;
  rewrite (handle_pts_to0 ts) (handle_pts_to ts)

let share_body
  (#opened: _)
  (r2: state_t)
: STGhostT unit opened
    (handle_pts_to_body r2)
    (fun _ -> handle_pts_to_body r2 `star` handle_pts_to_body r2)
= rewrite (handle_pts_to_body r2) (handle_pts_to_body0 r2);
  let _ = gen_elim () in
  let pa = vpattern_replace (fun pa -> A.pts_to r2.thread_locks pa _) in
  A.share r2.thread_locks pa (half_perm pa) (half_perm pa);
  R.share r2.state;
  M.core_inv_share _;
  M.frozen_logs_share _ _;
  rewrite (handle_pts_to_body0 r2) (handle_pts_to_body r2);
  noop ();
  rewrite (handle_pts_to_body0 r2) (handle_pts_to_body r2)

let share_aux
  (#opened: _)
  (r2: state_t)
: STGhostT unit opened
    (handle_pts_to_aux r2)
    (fun _ -> handle_pts_to_aux r2 `star` handle_pts_to_aux r2)
= rewrite (handle_pts_to_aux r2) (handle_pts_to_aux0 r2);
  let _ = gen_elim () in
  let r1 = vpattern_replace (fun r1 -> R.pts_to handle.state_ptr _ r1 `star` R.pts_to r1 _ _) in
  R.share handle.state_ptr;
  R.share r1;
  share_body r2;
  rewrite (handle_pts_to_aux0 r2) (handle_pts_to_aux r2);
  noop ();
  rewrite (handle_pts_to_aux0 r2) (handle_pts_to_aux r2)

let share
  ts
= rewrite (handle_pts_to ts) (handle_pts_to0 ts);
  let _ = gen_elim () in
  share_aux _;
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
  else exists_ handle_pts_to_aux

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
        let r2 = vpattern_replace_erased (fun r2 -> R.pts_to state _ r2 `star` handle_pts_to_body r2) in
        share_body _;
        R.share state;
        (* invariant *)
        rewrite
          (state_ptr_inv_not_null state)
          (state_ptr_inv_if state (half_perm p));
        rewrite
          (state_ptr_inv0 handle.state_ptr)
          (state_ptr_inv handle.state_ptr);
        (* handle_pts_to *)
        rewrite
          (handle_pts_to_aux0 r2)
          (handle_pts_to_aux0 r2);
        rewrite 
          (exists_ handle_pts_to_aux)
          (handle_is_null_post false);
        return false
      end
    )

let seq_lemma_index_upd
  (#a:Type)
  (s:Seq.seq a)
  (n:nat{n < Seq.length s})
  (v:a)
: Lemma
  (requires True)
  (ensures (forall i . Seq.index (Seq.upd s n v) i == (if i = n then v else Seq.index s i)))
= ()

// TODO: replace this function with a Steel.ST.Loops.while_loop
let rec init_thread_locks_loop
  (tl_state: Ghost.erased M.top_level_state)
  (tl_logs: Ghost.erased M.tid_log_map)
  (tl: A.array (thread_lock_t tl_state))
  (a0: Ghost.erased (Seq.seq (thread_lock_t tl_state)))
  (tid: U16.t)
: ST unit
    (M.all_logs tl_state tl_logs `star` A.pts_to tl full_perm a0)
    (fun _ ->
      exists_ (fun l' -> M.frozen_logs tl_state l') `star`
      exists_ (fun a ->
      A.pts_to tl full_perm a `star`
      pure (thread_state_prop a /\ Seq.length a == U32.v AT.n_threads)
    ))
    (A.length tl == U32.v AT.n_threads /\
      Seq.length (Ghost.reveal a0) == U32.v AT.n_threads /\
      U16.v tid <= U32.v AT.n_threads /\
      (forall (i: nat) . i < U16.v tid ==> U16.v (Ghost.reveal (dfst (Seq.index (Ghost.reveal a0) i))) == i) /\
      (forall (i: AT.tid) . U16.v i >= U16.v tid ==> Some? (Map.sel tl_logs i))
    )
    (fun _ -> True)
= let tid32 = FStar.Int.Cast.uint16_to_uint32 tid in
  if tid32 = AT.n_threads
  then begin
    M.freeze_all_logs _ _;
    return ()
  end
  else begin
    M.all_logs_log_of_tid _ _ tid ();
    let l = Lock.new_lock (thread_lock_vprop tl_state tid) in
    let t : thread_lock_t tl_state = (| Ghost.hide tid, l |) in
    A.write tl tid32 t;
    Seq.lemma_len_upd (U32.v tid32) t a0;
    seq_lemma_index_upd a0 (U32.v tid32) t;
    init_thread_locks_loop tl_state _ tl _ (tid `U16.add` 1us)
  end

let init_thread_locks
  (tl_state: Ghost.erased M.top_level_state)
  (tl_logs: Ghost.erased M.tid_log_map)
: ST (A.array (thread_lock_t tl_state))
    (M.all_logs tl_state tl_logs)
    (fun tl ->
      exists_ (fun l' -> M.frozen_logs tl_state l') `star`
      exists_ (fun a ->
        A.pts_to tl full_perm a `star`
        pure (thread_state_prop a /\ Seq.length a == U32.v AT.n_threads)
    ))
    (forall (i: AT.tid) . Some? (Map.sel tl_logs i))
    (fun _ -> True)
= M.all_logs_log_of_tid _ _ 0us ();
  let l0 = Lock.new_lock (thread_lock_vprop tl_state 0us) in
  let tl0: thread_lock_t tl_state = (| Ghost.hide 0us, l0 |) in
  let tl = A.alloc tl0 AT.n_threads in
  Seq.lemma_create_len (U32.v AT.n_threads) tl0;
  Seq.lemma_index_create (U32.v AT.n_threads) tl0 0;
  init_thread_locks_loop _ _ tl _ 1us;
  return tl

#push-options "--z3rlimit 32"
#restart-solver

let init ()
= Lock.acquire handle._lock;
  rewrite (state_ptr_lock handle.state_ptr) (state_ptr_lock0 handle.state_ptr);
  let _ = gen_elim () in
  let state = R.read handle.state_ptr in
  if R.is_null state
  then begin
    let r2_state = M.init () in
    let ts = elim_exists () in
    let tl = init_thread_locks ts _ in
    let _ = gen_elim () in
    let tl_f = vpattern_replace_erased (M.frozen_logs ts) in
    let tl_a = vpattern_replace_erased (A.pts_to tl _) in
    [@@inline_let]
    let r2 = ({
      state = r2_state;
      tl_state = ts;
      thread_locks = tl;
      tl_thread_locks = tl_a;
      tl_frozen_logs = tl_f;
      tl_prf = ();
    })
    in
    let state' = R.alloc r2 in
    R.pts_to_not_null state';
    rewrite (R.pts_to r2_state full_perm _) (R.pts_to r2.state full_perm r2.tl_state);
    rewrite (A.pts_to _ _ _) (A.pts_to r2.thread_locks full_perm r2.tl_thread_locks);
    rewrite (M.frozen_logs _ _) (M.frozen_logs r2.tl_state r2.tl_frozen_logs);
    rewrite (R.pts_to handle.state_ptr _ _) (R.pts_to handle.state_ptr (half_perm full_perm) state);
    vpattern_rewrite M.core_inv (Ghost.reveal r2.tl_state);
    rewrite (handle_pts_to_body0 r2) (handle_pts_to_body r2);
    share_body _;
    R.share state';
    with_invariant
      #unit
      #(R.pts_to handle.state_ptr (half_perm full_perm) state `star` R.pts_to state' (half_perm full_perm) r2 `star` handle_pts_to_body r2)
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
        rewrite
          (state_ptr_inv_not_null state')
          (state_ptr_inv_if state' full_perm);
        rewrite
          (state_ptr_inv0 handle.state_ptr)
          (state_ptr_inv handle.state_ptr);
        noop ()
      );
    R.share handle.state_ptr;
    rewrite (state_ptr_lock0 handle.state_ptr) (state_ptr_lock handle.state_ptr);
    Lock.release handle._lock;
    rewrite (handle_pts_to_aux0 r2) (handle_pts_to_aux r2);
    rewrite (handle_pts_to0 ts) (handle_pts_to ts);
    return true
  end else begin
    R.share handle.state_ptr;
    rewrite (state_ptr_lock0 handle.state_ptr) (state_ptr_lock handle.state_ptr);
    Lock.release handle._lock;
    let p = vpattern_replace (fun p -> R.pts_to handle.state_ptr p _) in
    rewrite (R.pts_to handle.state_ptr _ _) (R.pts_to handle.state_ptr p state);
    with_invariant_g
      #unit
      #(R.pts_to handle.state_ptr p state)
      #(fun _ -> exists_ (fun ts -> handle_pts_to ts))
      #_
      #(state_ptr_inv handle.state_ptr)
      handle._inv
      (fun _ ->
        rewrite (state_ptr_inv _) (state_ptr_inv0 handle.state_ptr);
        let _ = gen_elim () in
        R.gather _ #state handle.state_ptr;
        rewrite (state_ptr_inv_if _ _) (state_ptr_inv_not_null state);
        let _ = gen_elim () in
        R.share state;
        share_body _;
        let p' = vpattern_replace (fun p -> R.pts_to handle.state_ptr p _) in
        R.share handle.state_ptr;
        rewrite (state_ptr_inv_not_null state) (state_ptr_inv_if state p');
        rewrite (state_ptr_inv0 handle.state_ptr) (state_ptr_inv handle.state_ptr);
        let r2 = vpattern_replace (fun r2 -> R.pts_to state _ r2 `star` handle_pts_to_body r2) in
        let ts = Ghost.reveal r2.tl_state in
        rewrite (handle_pts_to_aux0 r2) (handle_pts_to_aux r2);
        rewrite (handle_pts_to0 ts) (handle_pts_to ts);
        noop ()
      );
    return false
  end

#pop-options

inline_for_extraction
let acquire_thread_lock
  (t: state_t)
  (tid: AT.tid)
: STT (Ghost.erased AEH.log)
    (handle_pts_to_body t)
    (fun entries -> handle_pts_to_body t `star` M.log_of_tid t.tl_state tid entries)
= rewrite (handle_pts_to_body t) (handle_pts_to_body0 t);
  let _ = gen_elim () in
  let l = A.read t.thread_locks (FStar.Int.Cast.uint16_to_uint32 tid) in
  Lock.acquire (dsnd l <: Lock.lock (thread_lock_vprop t.tl_state tid));
  let entries : Ghost.erased AEH.log = elim_exists () in
  rewrite (handle_pts_to_body0 t) (handle_pts_to_body t);
  return entries

inline_for_extraction
let release_thread_lock
  (t: state_t)
  (tid: AT.tid)
  (entries: Ghost.erased AEH.log)
: STT unit
    (handle_pts_to_body t `star` M.log_of_tid t.tl_state tid entries)
    (fun _ -> handle_pts_to_body t)
= rewrite (handle_pts_to_body t) (handle_pts_to_body0 t);
  let _ = gen_elim () in
  let l = A.read t.thread_locks (FStar.Int.Cast.uint16_to_uint32 tid) in
  Lock.release (dsnd l <: Lock.lock (thread_lock_vprop t.tl_state tid));
  rewrite (handle_pts_to_body0 t) (handle_pts_to_body t)

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
               (t0: Ghost.erased state_t)
               (tid:U16.t)
               (#log_perm:perm)
               (#log_bytes:Ghost.erased AT.bytes)
               (len: U32.t)
               (input: EXT.extern_ptr U8.t)
               (out_len: U32.t)
               (#out_bytes:Ghost.erased AT.bytes)
               (output: EXT.extern_ptr U8.t)
  : ST (verify_result len)
    (handle_pts_to_aux t0 `star` verify_pre log_perm log_bytes input out_bytes output)
    (fun res -> verify_post tid log_perm log_bytes len input out_len out_bytes output res)
    (check_verify_input tid len input out_len output)
    (fun _ -> True)
= rewrite (handle_pts_to_aux t0) (handle_pts_to_aux0 t0);
  let _ = gen_elim () in
  let r1 = R.read handle.state_ptr in
  vpattern_rewrite (fun r1 -> R.pts_to handle.state_ptr _ r1 `star` R.pts_to r1 _ _) r1;
  let r2 = R.read r1 in
  vpattern_rewrite (fun r2 -> R.pts_to r1 _ r2 `star` handle_pts_to_body r2) r2;
  let entries = acquire_thread_lock _ tid in
  rewrite (handle_pts_to_body r2) (handle_pts_to_body0 r2);
  let _ = gen_elim () in
  let input' = EXT.take input len in
  let output' = EXT.take output out_len in
  vpattern_rewrite (fun a -> A.pts_to a log_perm log_bytes) input';
  vpattern_rewrite (fun a -> A.pts_to a full_perm out_bytes) output';
  let v = M.verify_log _ tid len input' out_len output' in
  let res = Some v in
  let t = r2.tl_state in
  match v returns STT (verify_result len) (R.pts_to handle.state_ptr _ r1 `star` R.pts_to r1 _ r2 `star` R.pts_to r2.state _ _ `star` A.pts_to r2.thread_locks _ _ `star` M.frozen_logs _ _ `star` M.verify_post _ tid entries log_perm log_bytes len input' out_len out_bytes output' v) (fun res -> verify_post tid log_perm log_bytes len input out_len out_bytes output res) with
  | Some (V.Verify_success read wrote) ->
    rewrite
      (M.verify_post _ tid entries log_perm log_bytes len input' out_len out_bytes output' _)
      (M.core_inv r2.tl_state `star`
        A.pts_to (EXT.gtake input) log_perm log_bytes `star`
        exists_ (M.verify_post_success_pred t tid entries log_bytes out_len out_bytes output' read wrote)
      );
    let _ = gen_elim () in
    rewrite (handle_pts_to_body0 r2) (handle_pts_to_body r2);
    let entries' = vpattern_erased (fun entries' -> M.log_of_tid t tid (_ `Seq.append` entries')) in
    vpattern_rewrite (fun t -> M.log_of_tid t _ _) r2.tl_state;
    release_thread_lock _ tid _;
    rewrite (handle_pts_to_aux0 r2) (handle_pts_to_aux r2);
    rewrite (handle_pts_to0 t) (handle_pts_to t);
    let out_bytes' = vpattern_replace_erased (A.pts_to output' _) in
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
    m_verify_post_failure_eq r2.tl_state tid entries log_perm log_bytes len input' out_len out_bytes output' v;
    let _ = gen_elim () in
    rewrite (handle_pts_to_body0 r2) (handle_pts_to_body r2);
    vpattern_rewrite (fun t -> M.log_of_tid t _ _) r2.tl_state;
    release_thread_lock _ tid _;
    rewrite (handle_pts_to_aux0 r2) (handle_pts_to_aux r2);
    rewrite (handle_pts_to0 t) (handle_pts_to t);
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
    rewrite (handle_is_null_post _) (exists_ handle_pts_to_aux);
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
    rewrite (handle_is_null_post _) (exists_ handle_pts_to_aux);
    let t0 = elim_exists () in
    rewrite (handle_pts_to_aux t0) (handle_pts_to_aux0 t0);
    let _ = gen_elim () in
    let r1 = R.read handle.state_ptr in
    vpattern_rewrite (fun r1 -> R.pts_to handle.state_ptr _ r1 `star` R.pts_to r1 _ _) r1;
    let r2 = R.read r1 in
    vpattern_rewrite (fun r2 -> R.pts_to r1 _ r2 `star` handle_pts_to_body r2) r2;
    rewrite (handle_pts_to_body r2) (handle_pts_to_body0 r2);
    let _ = gen_elim () in
    let t = r2.tl_state in
    let r = M.max_certified_epoch r2.state in
    vpattern_rewrite (fun t -> M.read_max_post t _) t;
    rewrite (handle_pts_to_body0 r2) (handle_pts_to_body r2);
    rewrite (handle_pts_to_aux0 r2) (handle_pts_to_aux r2);
    rewrite (handle_pts_to0 t) (handle_pts_to t);
    let res = Some r in
    rewrite (max_certified_epoch_post_some r) (max_certified_epoch_post res);
    return res
  end

#pop-options
