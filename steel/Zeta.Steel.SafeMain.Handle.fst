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

noeq
type handle_t = {
  state: state_t;
  _inv: inv (handle_pts_to_body state);
}

let handle: handle_t =
  begin
    let r2_state = M.init () in
    let ts = elim_exists () in
    let tl = init_thread_locks ts _ in
    let _ = gen_elim () in
    let tl_f = vpattern_replace_erased (M.frozen_logs ts) in
    let tl_a = vpattern_replace_erased (A.pts_to tl _) in
    [@@inline_let]
    let r2 : state_t = ({
      state = r2_state;
      tl_state = ts;
      thread_locks = tl;
      tl_thread_locks = tl_a;
      tl_frozen_logs = tl_f;
      tl_prf = ();
    })
    in
    rewrite (R.pts_to r2_state full_perm _) (R.pts_to r2.state full_perm r2.tl_state);
    rewrite (A.pts_to _ _ _) (A.pts_to r2.thread_locks full_perm r2.tl_thread_locks);
    rewrite (M.frozen_logs _ _) (M.frozen_logs r2.tl_state r2.tl_frozen_logs);
    vpattern_rewrite M.core_inv (Ghost.reveal r2.tl_state);
    rewrite (handle_pts_to_body0 r2) (handle_pts_to_body r2);
    let i = new_invariant (handle_pts_to_body r2) in
    return ({
      state = r2;
      _inv = i;
    })
  end <: STT handle_t emp (fun _ -> emp)
