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
module Lock = Steel.ST.SpinLock
module TLM = Zeta.Steel.ThreadLogMap

module T = Zeta.Steel.FormatsManual
module M = Zeta.Steel.ThreadStateModel
module AEH = Zeta.Steel.AggregateEpochHashes
module V = Zeta.Steel.Verifier
module SA = Zeta.SeqAux

module Loops = Steel.ST.Loops

let init_thread_state
  (#m:TLM.repr)
  (mlogs:TLM.t)
  (i:tid)
  (_:squash (Map.sel m i == Some Seq.empty))
  : ST (thread_state mlogs)
       (TLM.tids_pts_to mlogs half m false)
       (fun st -> TLM.tids_pts_to mlogs half (Map.upd m i None) false)
       (requires True)
       (ensures fun st -> st.tid == i)
  = let st = VerifierSteps.create i in
    TLM.take_tid mlogs m i;
    rewrite
      (TLM.tid_pts_to _ _ _ _ _)
      (TLM.tid_pts_to mlogs
                      (M.init_thread_state_model i).M.thread_id
                      half
                      (M.init_thread_state_model i).M.processed_entries
                      false);
    intro_exists (M.init_thread_state_model i)
                 (fun tsm -> V.thread_state_inv st tsm
                            `star`
                          TLM.tid_pts_to mlogs tsm.M.thread_id half tsm.M.processed_entries false);
    rewrite
      (exists_ (fun tsm -> V.thread_state_inv st tsm
                          `star`
                        TLM.tid_pts_to mlogs tsm.M.thread_id half tsm.M.processed_entries false))    
      (thread_inv st mlogs);
    let lock = new_cancellable_lock (thread_inv st mlogs) in
    return ({tid = i; tsm = st; lock = lock})

let tid_positions_ok_until #l (all_threads:Seq.seq (thread_state l)) (i:nat)
  : prop
  = forall (j:SA.seq_index all_threads).
      j < i ==> (let sj = Seq.index all_threads j in
                 U16.v sj.tid == j)

let rec init_all_threads_state
  (#m:TLM.repr)
  (#mlogs:TLM.t)
  (all_threads:all_threads_t mlogs)
  (i:U16.t{U16.v i <= U32.v n_threads})
  : ST unit
       (TLM.tids_pts_to mlogs half m false
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
    let b = FStar.Int.Cast.uint16_to_uint32 i = n_threads in
    if b returns STT _ _ (fun _ -> exists_ (fun s -> A.pts_to all_threads full_perm s
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
      let st = init_thread_state mlogs i () in
      A.write all_threads (FStar.Int.Cast.uint16_to_uint32 i) st;
      rewrite
        (A.pts_to all_threads full_perm (Seq.upd s (U32.v (FStar.Int.Cast.uint16_to_uint32 i)) st))
        (A.pts_to all_threads full_perm (Seq.upd s (U16.v i) st));
      intro_pure (tid_positions_ok_until (Seq.upd s (U16.v i) st) (U16.v (U16.add i 1us)));
      intro_exists
        (Seq.upd s (U16.v i) st)
        (fun s -> A.pts_to all_threads full_perm s
                 `star`
               pure (tid_positions_ok_until s (U16.v (U16.add i 1us))));
      init_all_threads_state #(Map.upd m i None) #mlogs all_threads (U16.add i 1us)
    end

let init_aux (#opened:_)
  (aeh:AEH.aggregate_epoch_hashes)
  (all_threads:all_threads_t aeh.mlogs)
  (t:top_level_state)
  (s:Ghost.erased (Seq.seq (thread_state aeh.mlogs)))
  : STGhost unit opened
      (pure (tid_positions_ok s)
         `star`
       A.pts_to all_threads full_perm s
         `star`
       TLM.tids_pts_to aeh.mlogs half (Map.const (Some Seq.empty)) false)
      (fun _ -> core_inv t
               `star`
             TLM.tids_pts_to t.aeh.mlogs half (Map.const (Some Seq.empty)) false)
      (requires t.aeh == aeh /\ t.all_threads == all_threads)
      (ensures fun _ -> True)
  = rewrite (A.pts_to all_threads full_perm s)
            (A.pts_to t.all_threads full_perm s);
    rewrite (TLM.tids_pts_to aeh.mlogs half (Map.const (Some Seq.empty)) false)
            (TLM.tids_pts_to t.aeh.mlogs half (Map.const (Some Seq.empty)) false);
    rewrite (pure (tid_positions_ok s))
            (pure (tid_positions_ok #(t.aeh.mlogs) s));
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

let init () =
  let aeh = AEH.create () in
  TLM.share_tids_pts_to aeh.mlogs (Map.const (Some Seq.empty));
  let st0 = init_thread_state aeh.mlogs 0us () in
  let all_threads = A.alloc st0 n_threads in
  intro_pure (tid_positions_ok_until (Seq.create (U32.v n_threads) st0) 1);
  intro_exists
    (Seq.create (U32.v n_threads) st0)
    (fun s -> A.pts_to all_threads full_perm s
             `star`
           pure (tid_positions_ok_until s 1));
  init_all_threads_state
    #(Map.upd (Map.const (Some Seq.empty)) 0us None)
    #aeh.mlogs
    all_threads
    1us;

  let s = elim_exists () in
  A.pts_to_length all_threads s;
  elim_pure (tid_positions_ok_until s (Seq.length s));

  intro_pure (tid_positions_ok s);

  let r = ({ aeh = aeh; all_threads = all_threads }) in
  init_aux aeh all_threads r s;
  return r

let verify_log t tid #entries #log_perm #log_bytes len input out_len #out_bytes output =
  rewrite (core_inv t)
          (exists_ (fun perm -> exists_ (fun s ->
           A.pts_to t.all_threads perm s
             `star`
           pure (tid_positions_ok s))));
  let perm = elim_exists () in
  let s = elim_exists () in
  A.pts_to_length t.all_threads s;
  let st_tid = A.read t.all_threads (FStar.Int.Cast.uint16_to_uint32 tid) in

  let b = acquire st_tid.lock in

  match b returns STT _
                      (A.pts_to input log_perm log_bytes
                         `star`
                       A.pts_to output full_perm out_bytes
                         `star`
                       TLM.tid_pts_to _ _ _ _ _
                         `star`
                       A.pts_to t.all_threads perm s
                         `star`
                       pure (tid_positions_ok s)
                         `star`
                       maybe_acquired b st_tid.lock)
                      (verify_post
                         t
                         tid
                         entries
                         log_perm
                         log_bytes
                         len
                         input
                         out_len
                         out_bytes
                         output) with
  | false ->
    let r = None in
    rewrite (maybe_acquired false st_tid.lock)
            emp;
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
    intro_exists (Ghost.reveal out_bytes) (fun s -> A.pts_to output full_perm s);
    intro_exists (Ghost.reveal entries) (fun entries -> TLM.tid_pts_to t.aeh.mlogs tid half entries false);
    rewrite_with_tactic
      (exists_ (fun s -> A.pts_to output full_perm s)
         `star`
       (A.pts_to input log_perm log_bytes
          `star`
        (core_inv t
           `star`
         exists_ (fun entries -> TLM.tid_pts_to t.aeh.mlogs tid half entries false))))
      (core_inv t
         `star`
       A.pts_to input log_perm log_bytes
         `star`
       (exists_ (fun s -> A.pts_to output full_perm s)
          `star`
        exists_ (fun entries -> TLM.tid_pts_to t.aeh.mlogs tid half entries false)));
    rewrite
      (core_inv t
         `star`
       A.pts_to input log_perm log_bytes
         `star`
       (exists_ (fun s -> A.pts_to output full_perm s)
          `star`
        exists_ (fun entries -> TLM.tid_pts_to t.aeh.mlogs tid half entries false)))
      (verify_post t tid entries log_perm log_bytes len input out_len out_bytes output r);
    return r
  | _ ->
    rewrite (maybe_acquired _ _)
            (thread_inv st_tid.tsm t.aeh.mlogs
               `star`
             can_release st_tid.lock);
    rewrite (thread_inv st_tid.tsm t.aeh.mlogs)
            (exists_ (thread_inv_predicate st_tid.tsm t.aeh.mlogs));
    let tsm = elim_exists () in
    rewrite (thread_inv_predicate st_tid.tsm t.aeh.mlogs tsm)
            (V.thread_state_inv st_tid.tsm tsm
               `star`
             TLM.tid_pts_to t.aeh.mlogs tsm.M.thread_id half tsm.M.processed_entries false);

    assume (Ghost.reveal entries == tsm.M.processed_entries);
    assume (tsm.M.thread_id == tid);

    rewrite
      (TLM.tid_pts_to t.aeh.mlogs tid half entries false)
      (TLM.tid_pts_to t.aeh.mlogs tsm.M.thread_id half tsm.M.processed_entries false);

    TLM.gather_tid_pts_to t.aeh.mlogs;
  
    rewrite
      (TLM.tid_pts_to t.aeh.mlogs tsm.M.thread_id (sum_perm half half) tsm.M.processed_entries false)
      (TLM.tid_pts_to t.aeh.mlogs tsm.M.thread_id full tsm.M.processed_entries false);

    let vr = V.verify_log st_tid.tsm input output t.aeh in
    match vr returns STT _
                         (can_release _
                            `star`
                          (pure (tid_positions_ok _)
                             `star`
                           (A.pts_to t.all_threads _ _
                              `star`
                            (V.verify_post _ _ _ _ _ _ _
                               `star`
                             A.pts_to input _ _))))
                         (verify_post
                            t
                            tid
                            entries
                            log_perm
                            log_bytes
                            len
                            input
                            out_len
                            out_bytes
                            output) with
    | V.Verify_success read wrote -> admit___ ()

    | _ ->
      rewrite
        (V.verify_post _ _ _ _ _ _ _)
        (V.some_failure st_tid.tsm output t.aeh
           `star`
         pure (V.Parsing_failure? vr ==>
               ~ (LogEntry.can_parse_log_entry log_bytes (V.Parsing_failure?.log_pos vr))));
      cancel st_tid.lock;
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
      assume (V.thread_id st_tid.tsm == tid);
      rewrite
        (TLM.tid_pts_to t.aeh.mlogs (V.thread_id st_tid.tsm) full entries' false)
        (TLM.tid_pts_to t.aeh.mlogs tid full entries' false);
      TLM.share_tid_pts_to t.aeh.mlogs;
      drop (TLM.tid_pts_to t.aeh.mlogs tid (half_perm full) entries' false);
      rewrite
        (TLM.tid_pts_to t.aeh.mlogs tid (half_perm full) entries' false)
        (TLM.tid_pts_to t.aeh.mlogs tid half entries' false);
      intro_exists
        (Ghost.reveal entries')
        (fun entries' -> TLM.tid_pts_to t.aeh.mlogs tid half entries' false);
      rewrite_with_tactic
        (core_inv t
           `star`
         A.pts_to input log_perm log_bytes
           `star`
         exists_ (fun s -> A.pts_to output full_perm s)
            `star`
         exists_ (fun entries -> TLM.tid_pts_to t.aeh.mlogs tid half entries false))
        (core_inv t
           `star`
         A.pts_to input log_perm log_bytes
           `star`
         (exists_ (fun s -> A.pts_to output full_perm s)
            `star`
          exists_ (fun entries -> TLM.tid_pts_to t.aeh.mlogs tid half entries false)));
      let r = None in
      rewrite
        (core_inv t
           `star`
         A.pts_to input log_perm log_bytes
           `star`
         (exists_ (fun s -> A.pts_to output full_perm s)
            `star`
          exists_ (fun entries -> TLM.tid_pts_to t.aeh.mlogs tid half entries false)))
        (verify_post t tid entries log_perm log_bytes len input out_len out_bytes output r);
      return r

#set-options "--print_implicits"
