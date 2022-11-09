module Zeta.Steel.Main

open FStar.Ghost
open Zeta.Steel.ApplicationTypes
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
open Zeta.Steel.FormatsManual
open Steel.ST.Util
open Zeta.Steel.Util

module A = Steel.ST.Array
module G = Steel.ST.GhostReference
module Lock = Steel.ST.CancellableSpinLock
module TLM = Zeta.Steel.ThreadLogMap

module T = Zeta.Steel.FormatsManual
module M = Zeta.Steel.ThreadStateModel
module AEH = Zeta.Steel.AggregateEpochHashes
module V = Zeta.Steel.Verifier
module SA = Zeta.SeqAux

module Loops = Steel.ST.Loops

let lock_perm (b: Ghost.erased bool) : Tot perm =
  if b then half else full_perm

[@@ __reduce__]
let thread_inv_predicate
  (b: Ghost.erased bool)
  (t:V.thread_state_t)
  (mlogs:TLM.t)
  : M.thread_state_model -> vprop
  = fun tsm ->
    pure (~ tsm.failed)
      `star`
    V.thread_state_inv t tsm
      `star`
    TLM.tid_pts_to mlogs tsm.M.thread_id (lock_perm b) tsm.M.processed_entries false

let thread_inv
  (b: Ghost.erased bool)
  (t: V.thread_state_t)
  (mlogs: TLM.t)
  : vprop
  = exists_ (thread_inv_predicate b t mlogs)

[@@CAbstractStruct]
noeq
type thread_state (b: Ghost.erased bool) (mlogs:TLM.t) =
{
  tid: tid;
  tsm: V.thread_state_t;
  tsm_prf: squash (V.thread_id tsm == tid);
  lock : Lock.cancellable_lock (thread_inv b tsm mlogs)
}

let all_threads_t (b: Ghost.erased bool) (mlogs:TLM.t) =
  larray (thread_state b mlogs) n_threads

noeq
type top_level_state (b: Ghost.erased bool) = {
  aeh: AEH.aggregate_epoch_hashes;
  all_threads : all_threads_t b aeh.mlogs
}

let tid_positions_ok (#b: Ghost.erased bool) #l (all_threads: Seq.seq (thread_state b l))
  : prop
  = forall (i:SA.seq_index all_threads).
        let si = Seq.index all_threads i in
        U16.v si.tid == i

[@@__reduce__]
let core_inv0 (#b: Ghost.erased bool) (t:top_level_state b)
  : vprop
  = exists_ (fun perm ->
    exists_ (fun v ->
      A.pts_to t.all_threads perm v `star`
      pure (tid_positions_ok v)))

let core_inv t
  : vprop
  = core_inv0 t

let core_inv_share t =
  rewrite (core_inv t) (core_inv0 t);
  let _ = Steel.ST.GenElim.gen_elim () in
  let p = vpattern_replace (fun p -> A.pts_to t.all_threads p _) in
  A.share t.all_threads p (half_perm p) (half_perm p);
  rewrite (core_inv0 t) (core_inv t);
  noop ();
  rewrite (core_inv0 t) (core_inv t)

let core_inv_gather t =
  rewrite (core_inv t) (core_inv0 t);
  let _ = Steel.ST.GenElim.gen_elim () in
  let p1 = vpattern_replace (fun p1 -> A.pts_to t.all_threads p1 _) in
  rewrite (core_inv t) (core_inv0 t);
  let _ = Steel.ST.GenElim.gen_elim () in
  A.gather t.all_threads p1 _;
  rewrite (core_inv0 t) (core_inv t)

[@@__steel_reduce__; __reduce__]
let all_logs' (#b: Ghost.erased bool) (t:top_level_state b) (tlm:tid_log_map)
  : vprop
  = TLM.tids_pts_to t.aeh.mlogs (lock_perm b) tlm false

[@@__steel_reduce__; __reduce__]
let all_logs (t:top_level_state true) (tlm:tid_log_map)
  : vprop
= all_logs' t tlm

[@@__steel_reduce__; __reduce__]
let log_of_tid (t:top_level_state true) (tid:tid) (l:M.log)
  : vprop
  = TLM.tid_pts_to t.aeh.mlogs tid half l false

[@@__steel_reduce__; __reduce__]
let snapshot (#b: Ghost.erased bool) (t:top_level_state b) (tlm:tid_log_map)
  : vprop
  = TLM.global_snapshot t.aeh.mlogs tlm

let init_thread_state
  (#m:Ghost.erased (TLM.repr))
  (b: Ghost.erased bool)
  (mlogs:TLM.t)
  (i:tid)
  (_:squash (Map.sel m i == Some Seq.empty))
  : ST (thread_state b mlogs)
       (TLM.tids_pts_to mlogs (lock_perm b) m false)
       (fun st -> TLM.tids_pts_to mlogs (lock_perm b) (Map.upd m i None) false)
       (requires True)
       (ensures fun st -> st.tid == i)
  = let st = VerifierSteps.create i in
    TLM.take_tid mlogs m i;
    rewrite
      (TLM.tid_pts_to _ _ _ _ _)
      (TLM.tid_pts_to mlogs
                      (M.init_thread_state_model i).M.thread_id
                      (lock_perm b)
                      (M.init_thread_state_model i).M.processed_entries
                      false);
    intro_pure (~ (M.init_thread_state_model i).M.failed);
    intro_exists (M.init_thread_state_model i)
                 (thread_inv_predicate b st mlogs);
    rewrite
      (exists_ (thread_inv_predicate b st mlogs))
      (thread_inv b st mlogs);
    let lock = Lock.new_cancellable_lock (thread_inv b st mlogs) in
    return ({tid = i; tsm = st; tsm_prf = (); lock = lock})

let tid_positions_ok_until (#b: Ghost.erased bool) #l (all_threads:Seq.seq (thread_state b l)) (i:nat)
  : prop
  = forall (j:SA.seq_index all_threads).
      j < i ==> (let sj = Seq.index all_threads j in
                 U16.v sj.tid == j)


let rec init_all_threads_state
  (#m:Ghost.erased (TLM.repr))
  (#b: Ghost.erased bool)
  (#mlogs:TLM.t)
  (all_threads:all_threads_t b mlogs)
  (i:U16.t{U16.v i <= U32.v n_threads})
  : ST unit
       (TLM.tids_pts_to mlogs (lock_perm b) m false
          `star`
        exists_ (fun s -> A.pts_to all_threads full_perm s
                         `star`
                       pure (tid_positions_ok_until s (U16.v i))))
       (fun _ -> exists_ (fun s -> A.pts_to all_threads full_perm s
                               `star`
                             pure (tid_positions_ok_until s (Seq.length s))))
       (requires forall (j:tid). U16.v i <= U16.v j ==> Map.sel m j == Some Seq.empty)
       (ensures fun _ -> True)
  = let s = elim_exists () in
    A.pts_to_length all_threads s;
    elim_pure (tid_positions_ok_until s (U16.v i));
    let check = FStar.Int.Cast.uint16_to_uint32 i = n_threads in
    if check returns STT _ _ (fun _ -> exists_ (fun s -> A.pts_to all_threads full_perm s
                                  `star`
                                pure (tid_positions_ok_until s (Seq.length s))))
    then begin
      intro_pure (tid_positions_ok_until s (Seq.length s));
      drop (TLM.tids_pts_to _ _ _ _);
      intro_exists
        (Ghost.reveal s)
        (fun s -> A.pts_to all_threads full_perm s
                 `star`
               pure (tid_positions_ok_until s (Seq.length s)));
      return ()
    end
    else begin
      let st = init_thread_state b mlogs i () in
      A.write all_threads (u16_as_size_t i) st;
      rewrite
        (A.pts_to all_threads full_perm (Seq.upd s (U32.v (FStar.Int.Cast.uint16_to_uint32 i)) st))
        (A.pts_to all_threads full_perm (Seq.upd s (U16.v i) st));
      intro_pure (tid_positions_ok_until (Seq.upd s (U16.v i) st) (U16.v (U16.add i 1us)));
      intro_exists
        (Seq.upd s (U16.v i) st)
        (fun s -> A.pts_to all_threads full_perm s
                 `star`
               pure (tid_positions_ok_until s (U16.v (U16.add i 1us))));
      init_all_threads_state #(Map.upd m i None) #b #mlogs all_threads (U16.add i 1us)
    end

let init_aux (#opened:_)
  (aeh:AEH.aggregate_epoch_hashes)
  (#b: Ghost.erased bool)
  (all_threads:all_threads_t b aeh.mlogs)
  (t:top_level_state b)
  (s:Ghost.erased (Seq.seq (thread_state b aeh.mlogs)))
  : STGhost unit opened
      (pure (tid_positions_ok s)
         `star`
       A.pts_to all_threads full_perm s
      )
//         `star`
//       TLM.tids_pts_to aeh.mlogs half (Map.const (Some Seq.empty)) false)
      (fun _ -> core_inv t
      )
//               `star`
//             TLM.tids_pts_to t.aeh.mlogs half (Map.const (Some Seq.empty)) false)
      (requires t.aeh == aeh /\ t.all_threads == all_threads)
      (ensures fun _ -> True)
  = rewrite (A.pts_to all_threads full_perm s)
            (A.pts_to t.all_threads full_perm s);
//    rewrite (TLM.tids_pts_to aeh.mlogs half (Map.const (Some Seq.empty)) false)
//            (TLM.tids_pts_to t.aeh.mlogs half (Map.const (Some Seq.empty)) false);
    rewrite (pure (tid_positions_ok s))
            (pure (tid_positions_ok #b #(t.aeh.mlogs) s));
    intro_exists
      (Ghost.reveal s)
      (fun s -> A.pts_to t.all_threads full_perm s
               `star`
             pure (tid_positions_ok s));
    intro_exists
      full_perm
      (fun perm -> exists_ (fun s -> A.pts_to t.all_threads perm s
                                 `star`
                               pure (tid_positions_ok s)));
    rewrite (exists_ _) (core_inv t)

let share_tids_pts_to_post
  (x: TLM.t)
  (m: TLM.repr)
  (b: Ghost.erased bool)
: vprop
= if b
  then TLM.tids_pts_to x (lock_perm b) m false
  else emp

let share_tids_pts_to
  (#o: _)
  (x: TLM.t)
  (m: TLM.repr)
  (b: Ghost.erased bool)
: STGhostT unit o
  (TLM.tids_pts_to x full_perm m false)
  (fun _ -> TLM.tids_pts_to x (lock_perm b) m false `star`
     share_tids_pts_to_post x m b
  )
= if b
  then begin
    TLM.share_tids_pts_to x m;
    rewrite (TLM.tids_pts_to x _ m false `star` TLM.tids_pts_to x _ m false)
      (TLM.tids_pts_to x (lock_perm b) m false `star` share_tids_pts_to_post x m b)
  end else begin
    rewrite (TLM.tids_pts_to x _ m false) (TLM.tids_pts_to x (lock_perm b) m false);
    rewrite emp (share_tids_pts_to_post x m b)
  end

let init b =
  let aeh = AEH.create () in
  share_tids_pts_to aeh.mlogs (Map.const (Some Seq.empty)) b;
  let st0 = init_thread_state b aeh.mlogs 0us () in
  let all_threads = A.alloc st0 (SizeT.uint32_to_sizet n_threads) in
  intro_pure (tid_positions_ok_until (Seq.create (U32.v n_threads) st0) 1);
  intro_exists
    (Seq.create (U32.v n_threads) st0)
    (fun s -> A.pts_to all_threads full_perm s
             `star`
           pure (tid_positions_ok_until s 1));
  init_all_threads_state
    #(Map.upd (Map.const (Some Seq.empty)) 0us None)
    #b
    #aeh.mlogs
    all_threads
    1us;

  let s = elim_exists () in
  A.pts_to_length all_threads s;
  elim_pure (tid_positions_ok_until s (Seq.length s));

  intro_pure (tid_positions_ok s);

  let r = ({ aeh = aeh; all_threads = all_threads }) in
  init_aux aeh all_threads r s;
  let t = R.alloc r in
  rewrite (share_tids_pts_to_post _ _ _) (init_post r);
  return t

let exists_log_of_tid_gen_intro
  (#opened: _)
  (#b: Ghost.erased bool)
  (t: top_level_state b)
  (tid: tid)
  (entries: AEH.log)
: STGhostT unit opened
    (log_of_tid_gen t tid entries)
    (fun _ -> exists_log_of_tid_gen t tid)
= if b returns STGhostT unit opened
    (log_of_tid_gen t tid entries)
    (fun _ -> exists_log_of_tid_gen t tid)
  then begin
    rewrite (log_of_tid_gen t tid entries) (log_of_tid t tid entries);
    rewrite (exists_log_of_tid t tid) (exists_log_of_tid_gen t tid)
  end else begin
    rewrite (log_of_tid_gen t tid entries) (exists_log_of_tid_gen t tid)
  end

inline_for_extraction
noextract
let steel_ifthenelse
  (#t: Type)
  (#vpre: vprop)
  (#vpost: (t -> vprop))
  (b: bool)
  (ttrue: (squash (b == true) -> STT t vpre vpost))
  (tfalse: (squash (b == false) -> STT t vpre vpost))
: STF t vpre vpost True (fun _ -> True)
= if b then ttrue () else tfalse ()

inline_for_extraction
noextract
let steel_ifthenelse_not
  (#t: Type)
  (#vpre: vprop)
  (#vpost: (t -> vprop))
  (b: bool)
  (tfalse: (squash (b == false) -> STT t vpre vpost))
  (ttrue: (squash (b == true) -> STT t vpre vpost))
: STF t vpre vpost True (fun _ -> True)
= if b then ttrue () else tfalse ()

let gather_thread_logs
  (#opened: _)
  (incremental: Ghost.erased bool)
  (t: top_level_state incremental)
  (tid: tid)
  (entries1 entries2: AEH.log)
: STGhost unit opened
    (TLM.tid_pts_to t.aeh.mlogs tid (lock_perm incremental) entries1 false `star`
      log_of_tid_gen #incremental t tid entries2)
    (fun _ -> TLM.tid_pts_to t.aeh.mlogs tid full entries1 false)
    True
    (fun _ -> Ghost.reveal incremental == true ==> entries1 == entries2)
=
  if incremental
  then begin
    rewrite (log_of_tid_gen _ _ _) (TLM.tid_pts_to t.aeh.mlogs tid half entries2 false);
    TLM.gather_tid_pts_to #_ #_ #(lock_perm incremental) t.aeh.mlogs;
    vpattern_rewrite (fun p -> TLM.tid_pts_to t.aeh.mlogs tid p entries1 false) full
  end else begin
    vpattern_rewrite (fun p -> TLM.tid_pts_to t.aeh.mlogs tid p entries1 false) full;
    rewrite (log_of_tid_gen _ _ _) emp
  end

let share_thread_logs
  (#opened: _)
  (incremental: Ghost.erased bool)
  (t: top_level_state incremental)
  (tid: tid)
  (entries: AEH.log)
: STGhostT unit opened
    (TLM.tid_pts_to t.aeh.mlogs tid full entries false)
    (fun _ -> TLM.tid_pts_to t.aeh.mlogs tid (lock_perm incremental) entries false `star`
      log_of_tid_gen #incremental t tid entries)
= if incremental
  then begin
    TLM.share_tid_pts_to t.aeh.mlogs;
    rewrite (TLM.tid_pts_to _ _ _ _ _) (log_of_tid_gen #incremental t tid entries);
    vpattern_rewrite (fun p -> TLM.tid_pts_to _ _ p _ _) (lock_perm incremental)
  end else begin
    vpattern_rewrite (fun p -> TLM.tid_pts_to _ _ p _ _) (lock_perm incremental);
    rewrite emp  (log_of_tid_gen #incremental t tid entries)
  end

let verify_log_aux (#incremental: Ghost.erased bool)
                   (t:top_level_state incremental)
                   (tid:tid)
                   (#entries:erased AEH.log)
                   (#log_perm:perm)
                   (#log_bytes:erased bytes)
                   (len: U32.t { len <> 0ul })
                   (input:larray U8.t len)
                   (out_len: U32.t)
                   (#out_bytes:erased bytes)
                   (output:larray U8.t out_len)
 : STT (option (verify_result len))
    (core_inv t `star`
     A.pts_to input log_perm log_bytes `star`
     A.pts_to output full_perm out_bytes `star`
     log_of_tid_gen t tid entries)
    (verify_post t tid entries log_perm log_bytes len input out_len out_bytes output)
 = rewrite (core_inv t) (core_inv0 t);
  let perm = elim_exists () in
  let s = elim_exists () in
  let sq : squash (tid_positions_ok s) = elim_pure (tid_positions_ok s) in

  A.pts_to_length t.all_threads s;
  let st_tid : thread_state incremental t.aeh.mlogs = A.read t.all_threads (u16_as_size_t tid) in

  let b = Lock.acquire #(thread_inv incremental st_tid.tsm t.aeh.mlogs) st_tid.lock in

  steel_ifthenelse_not
    b
    (fun _ ->
    //
    //Acquiring the lock for this thread's local state failed
    //This indicates an earlier failure
    //Reestablish the inv. and return
    //

    noop ();
    let r : option (verify_result len) = None in
    rewrite (Lock.maybe_acquired b st_tid.lock) emp;

    intro_exists (Ghost.reveal s)
                 (fun s -> A.pts_to t.all_threads perm s
                          `star`
                        pure (tid_positions_ok s));
    intro_exists (Ghost.reveal perm)
                 (fun perm -> exists_ (fun s -> A.pts_to t.all_threads perm s
                                            `star`
                                          pure (tid_positions_ok s)));
    rewrite
      (exists_ (fun perm -> exists_ (fun s -> A.pts_to t.all_threads perm s
                                          `star`
                                        pure (tid_positions_ok s))))
      (core_inv t);
    intro_exists
      (Ghost.reveal out_bytes)
      (fun s -> A.pts_to output full_perm s);

    exists_log_of_tid_gen_intro t tid entries;

    rewrite
      (core_inv t
         `star`
       A.pts_to input log_perm log_bytes
         `star`
       (exists_ (fun s -> A.pts_to output full_perm s)
          `star`
        exists_log_of_tid_gen t tid))
      (verify_post t tid entries log_perm log_bytes len input out_len out_bytes output r);

    return r

    )

    (fun _ ->

    rewrite (Lock.maybe_acquired _ _)
            (thread_inv incremental st_tid.tsm t.aeh.mlogs
               `star`
             Lock.can_release st_tid.lock);
    rewrite (thread_inv incremental st_tid.tsm t.aeh.mlogs)
            (exists_ (thread_inv_predicate incremental st_tid.tsm t.aeh.mlogs));
    let tsm = elim_exists () in

    elim_pure (~ tsm.M.failed);

    VerifierTypes.extract_tsm_entries_invariant st_tid.tsm;

    rewrite
      (log_of_tid_gen #incremental t tid entries)
      (log_of_tid_gen #incremental t tsm.M.thread_id entries);

    gather_thread_logs _ _ _ _ _;

    //
    //Call into the single-threaded verifier
    //

    let vr = V.verify_log st_tid.tsm input output t.aeh in

    steel_ifthenelse (V.Verify_success? vr)

    (fun _ ->

      let V.Verify_success read wrote = vr in

      rewrite
        (V.verify_post _ _ _ _ _ _ _)
        (exists_ (V.verify_post_success_pred tsm st_tid.tsm log_bytes out_bytes output t.aeh read wrote));


      let log = elim_exists () in
      M.verify_model_thread_id_inv tsm log;  //to get the following assertion about thread id
      assert ((M.verify_model tsm log).thread_id == tid);

      //
      //Verifier success means that the verifier returns
      //  something that's consistent with the spec
      //But it could be that the spec failed
      //So, a runtime check to make sure it indeed succeeded
      //
      let b_failed = VerifierSteps.check_failed st_tid.tsm in

      steel_ifthenelse b_failed

      (fun _ ->
        //
        //Similar to the case of lock failure,
        //  establish the invariant and return
        //
        Lock.cancel st_tid.lock;

        intro_exists (Ghost.reveal s)
                     (fun s -> A.pts_to t.all_threads perm s
                              `star`
                            pure (tid_positions_ok s));
        intro_exists (Ghost.reveal perm)
                     (fun perm -> exists_ (fun s -> A.pts_to t.all_threads perm s
                                                `star`
                                              pure (tid_positions_ok s)));
        rewrite
          (exists_ (fun perm -> exists_ (fun s -> A.pts_to t.all_threads perm s
                                              `star`
                                            pure (tid_positions_ok s))))
          (core_inv t);

        let out_bytes1 = elim_exists () in
        elim_pure (Application.n_out_bytes _ _ _ _ _ _);
        drop (pure _);
        intro_exists
          (Ghost.reveal out_bytes1)
          (fun s -> A.pts_to output full_perm s);

        share_thread_logs _ _ _ _;

        vpattern_rewrite (fun tid -> log_of_tid_gen _ tid _) tid;
        exists_log_of_tid_gen_intro _ _ _;

        drop (TLM.tid_pts_to _ _ _ _ _);
        drop (V.thread_state_inv _ _);

        let res = None in
        rewrite
          (core_inv t
             `star`
           A.pts_to input log_perm log_bytes
             `star`
           (exists_ (fun s -> A.pts_to output full_perm s)
              `star`
            exists_log_of_tid_gen t tid
          ))
          (verify_post t tid entries log_perm log_bytes len input out_len out_bytes output res);
        return res
      )


      (fun _ ->

        //Now we know that all is well
        //
        assert (not (M.verify_model tsm log).M.failed);
        share_thread_logs _ _ _ _;

        intro_pure (~ (M.verify_model tsm log).M.failed);
        intro_exists (M.verify_model tsm log) (thread_inv_predicate incremental st_tid.tsm   t.aeh.mlogs);
        Lock.release st_tid.lock;

        intro_exists (Ghost.reveal s)
                     (fun s -> A.pts_to t.all_threads perm s
                              `star`
                            pure (tid_positions_ok s));
        intro_exists (Ghost.reveal perm)
                     (fun perm -> exists_ (fun s -> A.pts_to t.all_threads perm s
                                                `star`
                                              pure (tid_positions_ok s)));
        rewrite
          (exists_ (fun perm -> exists_ (fun s -> A.pts_to t.all_threads perm s
                                              `star`
                                            pure (tid_positions_ok s))))
          (core_inv t);
        let out_bytes' = elim_exists () in
        elim_pure _;
        elim_pure _;

        assert (Ghost.reveal incremental == true ==> tsm.M.processed_entries == Ghost.reveal entries);
        M.verify_model_append tsm log;
        assert ((M.verify_model tsm log).processed_entries == Seq.append tsm.M.processed_entries log);

        rewrite
          (log_of_tid_gen _ _ _)
          (log_of_tid_gen t tid (entries `Seq.append` log)); // works because if incremental == false, then both sides are emp

        intro_pure (verify_post_success_pure_inv
                      incremental
                      tid
                      entries
                      log_bytes
                      out_bytes
                      read
                      wrote
                      (Ghost.reveal log)
                      out_bytes');

        intro_exists
          (Ghost.reveal out_bytes')
          (verify_post_success_out_bytes_pred t tid entries log_bytes out_len   out_bytes output read wrote log);
        intro_exists
          (Ghost.reveal log)
          (verify_post_success_pred t tid entries log_bytes out_len out_bytes output read wrote);
        let res = Some vr in
        rewrite
          (core_inv t
             `star`
           A.pts_to input log_perm log_bytes
             `star`
           exists_ (verify_post_success_pred t tid entries log_bytes out_len out_bytes output read wrote))
          (verify_post t tid entries log_perm log_bytes len input out_len out_bytes output res);
        return res
      )

    )

    (fun _ ->
      //
      //Single-threaded verifier failed
      //
      rewrite
        (V.verify_post _ _ _ _ _ _ _)
        (V.some_failure st_tid.tsm output t.aeh
           `star`
         pure (V.Parsing_failure? vr ==>
               ~ (LogEntry.can_parse_log_entry log_bytes (V.Parsing_failure?.log_pos vr))));
      Lock.cancel st_tid.lock;
      intro_exists (Ghost.reveal s)
                   (fun s -> A.pts_to t.all_threads perm s
                            `star`
                          pure (tid_positions_ok s));
      intro_exists (Ghost.reveal perm)
                   (fun perm -> exists_ (fun s -> A.pts_to t.all_threads perm s
                                              `star`
                                            pure (tid_positions_ok s)));
      rewrite
        (exists_ (fun perm -> exists_ (fun s -> A.pts_to t.all_threads perm s
                                            `star`
                                          pure (tid_positions_ok s))))
        (core_inv t);
      elim_pure _;
      //drop thread_state_inv
      drop (exists_ (V.thread_state_inv st_tid.tsm));

      let entries' = elim_exists #_ #_
        #(fun entries' -> TLM.tid_pts_to t.aeh.mlogs (V.thread_id st_tid.tsm) full entries' false)
        () in
      share_thread_logs _ _ _ _;
      drop (TLM.tid_pts_to _ _ _ _ _);
      exists_log_of_tid_gen_intro _ _ _;
      let r = None in
      rewrite
        (core_inv t
           `star`
         A.pts_to input log_perm log_bytes
           `star`
         (exists_ (fun s -> A.pts_to output full_perm s)
            `star`
          exists_log_of_tid_gen _ _
         ))
        (verify_post t tid entries log_perm log_bytes len input out_len out_bytes output r);
      return r

    )

 )

let verify_log
  #p #b #t r tid #entries #log_perm #log_bytes len input out_len #out_bytes output
  = let t' = R.read r in
    rewrite (core_inv t) (core_inv t');
    rewrite (log_of_tid_gen t tid entries) (log_of_tid_gen t' tid entries);
    let res = verify_log_aux t' tid len input out_len output in
    rewrite
      (verify_post t' tid entries log_perm log_bytes len input out_len out_bytes output res)
      (verify_post t tid entries log_perm log_bytes len input out_len out_bytes output res);
    return res

let max_certified_epoch
  #p #b #t r
  = let t' = R.read r in
    let res = AEH.advance_and_read_max_certified_epoch t'.aeh in
    assert_ (AEH.read_max_post t'.aeh res);
    match res with
    | AEH.Read_max_error ->
      rewrite (AEH.read_max_post t'.aeh res)
              (read_max_post t AEH.Read_max_error);
      return AEH.Read_max_error
    | AEH.Read_max_none ->
      rewrite (AEH.read_max_post t'.aeh res)
              (read_max_post t AEH.Read_max_none);
      return AEH.Read_max_none
    | AEH.Read_max_some max ->
      rewrite (AEH.read_max_post t'.aeh res)
              (AEH.read_max_post t'.aeh (AEH.Read_max_some max));

      let logs = elim_exists () in
      assert_ (snapshot t' (AEH.map_of_seq logs));
      rewrite (snapshot t' (AEH.map_of_seq logs))
              (snapshot t (AEH.map_of_seq logs));
      elim_pure _;
      Zeta.Correctness.main_theorem max logs;
      intro_pure (Zeta.Correctness.sequentially_consistent_app_entries_except_if_hash_collision logs max);
      intro_exists_erased logs (fun logs ->
        snapshot t (AEH.map_of_seq logs) `star`
        pure (Zeta.Correctness.sequentially_consistent_app_entries_except_if_hash_collision logs max));
      return (AEH.Read_max_some max)

// for dependencies only, to extract references
module C = C
