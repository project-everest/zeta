module Zeta.Steel.Verifier
open Zeta.Steel.VerifierTypes
open FStar.Ghost
open Steel.ST.Util
module G = Steel.ST.GhostReference
module R = Steel.ST.Reference
module A = Steel.ST.Array
module TLM = Zeta.Steel.ThreadLogMap
open Zeta.Steel.ApplicationTypes
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
open Zeta.Steel.FormatsManual
open Zeta.Steel.Util
module T = Zeta.Steel.FormatsManual
module M = Zeta.Steel.ThreadStateModel
module AEH = Zeta.Steel.AggregateEpochHashes
module P = Zeta.Steel.Parser
module Cast = FStar.Int.Cast
open Zeta.Steel.EpochHashes
module Application = Zeta.Steel.Application
#push-options "--ide_id_info_off"

let rewrite_with #o (p q:vprop) (_ : squash (p == q))
  : STGhostT unit o p (fun _ -> q)
  = rewrite p q

let compat_with_any_anchor_of_le (l:TLM.log)
                                 (le:log_entry { not (VerifyEpoch? le) })
  : Lemma (l `TLM.log_grows` (Seq.snoc l le) /\
           (Seq.snoc l le) `TLM.compat_with_any_anchor_of` l)
          [SMTPat (Seq.snoc l le)]
  = M.committed_entries_prefix (Seq.snoc l le);
    assert (Zeta.SeqAux.prefix (Seq.snoc l le) (Seq.length l) `Seq.equal` l)

let fail (#p:prop)
         (#tsm:M.thread_state_model)
         (#entries:erased _)
         (t:thread_state_t)
         (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
         (#outlen:U32.t)
         (#out_bytes:erased _)
         (out:larray U8.t outlen) //out array, to write outputs
  : STT unit
    (thread_state_inv t tsm `star`
     TLM.tid_pts_to aeh.mlogs tsm.thread_id full entries false `star`
     array_pts_to out out_bytes `star`
     pure p)
    (fun _ ->
      some_failure t out aeh)
  = elim_pure _;
    extract_tsm_entries_invariant t;
    rewrite (TLM.tid_pts_to _ _ _ _ _)
            (TLM.tid_pts_to aeh.mlogs (VerifierTypes.thread_id t) full entries false);
    intro_exists _ (thread_state_inv t);
    intro_exists _ (fun entries -> TLM.tid_pts_to aeh.mlogs _ full entries false);
    intro_exists _ (array_pts_to out);
    ()

let intro_nout_bytes (#o:_)
                     (tsm tsm':M.thread_state_model)
                     (out_bytes:erased bytes)
                     (out_offset:U32.t { U32.v out_offset <= Seq.length out_bytes })
  : STGhost unit o
    emp
    (fun _ -> pure (Application.n_out_bytes tsm tsm' out_offset 0ul out_bytes out_bytes))
    (requires M.delta_out_bytes tsm tsm' == Seq.empty)
    (ensures fun _ -> True)
  = intro_pure (Application.n_out_bytes tsm tsm' out_offset 0ul out_bytes out_bytes)

let verify_log_entry_post (tsm:M.thread_state_model)
                          (t:thread_state_t)
                          (out_bytes0:bytes)
                          (out_offset:U32.t)
                          (out:A.array U8.t) //out array, to write outputs
                          (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
                          (le:LogEntry.log_entry)
                          ([@@@smt_fallback] res:option U32.t)
  : vprop
  = match res with
    | None ->
         //if it fails, you still get back ownership on the various
         //resources, e.g., to free them
         //but not much else
         some_failure t out aeh

    | Some n_out ->
         //it succeeded
         let tsm' = M.verify_step_model tsm le in
         exists_ (fun (out_bytes1:Seq.seq U8.t) ->
           thread_state_inv t tsm' `star` //tsm' is the new state of the thread
           array_pts_to out out_bytes1 `star`  //the out array contains out_bytes
           TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm'.processed_entries false `star` //my contributions are updated
           pure (Application.n_out_bytes tsm tsm' out_offset n_out out_bytes0 out_bytes1))

let success (#o:_)
            (#tsm:M.thread_state_model)
            (t:thread_state_t)
            (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
            (#out_bytes0 #out_bytes1:erased _)
            (out_offset:U32.t)
            (out:A.array U8.t)
            (le:log_entry)
            (n_out:U32.t)
  : STGhostT unit o
    (thread_state_inv t (M.verify_step_model tsm le) `star`
     TLM.tid_pts_to aeh.mlogs tsm.thread_id full (M.verify_step_model tsm le).processed_entries false `star`
     array_pts_to out out_bytes1 `star`
     pure (Application.n_out_bytes tsm (M.verify_step_model tsm le) out_offset n_out out_bytes0 out_bytes1))
    (fun _ ->
      verify_log_entry_post tsm t out_bytes0 out_offset out aeh le (Some n_out))
  = let tsm' = M.verify_step_model tsm le in
    intro_exists_erased out_bytes1
       (fun (out_bytes1:Seq.seq U8.t) ->
         thread_state_inv t tsm' `star` //tsm' is the new state of the thread
         array_pts_to out out_bytes1 `star`  //the out array contains out_bytes
         TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm'.processed_entries false `star` //my contributions are updated
         pure (Application.n_out_bytes tsm tsm' out_offset n_out out_bytes0 out_bytes1))

val verify_entry_cases (#tsm:M.thread_state_model)
                       (t:thread_state_t) //handle to the thread state
                       (#outlen:U32.t)
                       (#out_bytes0:erased bytes)
                       (out_offset:U32.t { U32.v out_offset <= Seq.length out_bytes0 })
                       (out:larray U8.t outlen) //out array, to write outputs
                       (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
                       (le:LogEntry.log_entry)
                       (b:bool)
  : ST (option U32.t)
    (thread_state_inv t (update_if b tsm (M.verify_step_model tsm le)) `star`
     TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false `star`
     array_pts_to out out_bytes0)
    (fun res -> verify_log_entry_post tsm t out_bytes0 out_offset out aeh le res)
    (requires
      not (VerifyEpoch? le) /\ not (RunApp? le) /\
      not tsm.failed)
    (ensures fun _ -> True)

//fusing val and let leads to errors
let verify_entry_cases (#tsm:M.thread_state_model)
                       (t:thread_state_t) //handle to the thread state
                       (#outlen:U32.t)
                       (#out_bytes0:erased bytes)
                       (out_offset:U32.t { U32.v out_offset <= Seq.length out_bytes0 })
                       (out:larray U8.t outlen) //out array, to write outputs
                       (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
                       (le:LogEntry.log_entry)
                       (b:bool)
  = compat_with_any_anchor_of_le tsm.processed_entries le;
    TLM.update_tid_log aeh.mlogs tsm.thread_id tsm.processed_entries (M.verify_step_model tsm le).processed_entries;
    M.delta_out_bytes_not_runapp tsm le;
    intro_nout_bytes tsm (M.verify_step_model tsm le) out_bytes0 out_offset;
    if b
    then (
      rewrite (thread_state_inv t _)
              (thread_state_inv t (M.verify_step_model tsm le));
      success t aeh out_offset out le 0ul;
      return (Some 0ul)
    )
    else (
      rewrite (thread_state_inv t _)
              (thread_state_inv t tsm);
      fail t aeh out;
      return None
    )

#push-options "--query_stats --fuel 0 --ifuel 1 --z3rlimit_factor 3"
let verify_log_entry (#tsm:M.thread_state_model)
                     (t:thread_state_t) //handle to the thread state
                     (#outlen:U32.t)
                     (#out_bytes:erased bytes)
                     (out_offset:U32.t { U32.v out_offset <= Seq.length out_bytes })
                     (out:larray U8.t outlen) //out array, to write outputs
                     (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
                     (le:LogEntry.log_entry)
  : ST (option U32.t)
    (//precondition
      thread_state_inv t tsm `star`
      array_pts_to out out_bytes `star`
      TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false)
    (fun res -> //postcondition
      verify_log_entry_post tsm t out_bytes out_offset out aeh le res)
    (requires not tsm.failed /\
              not (RunApp? le))
    (ensures fun _ -> True)
   = match le with
     | VerifyEpoch ->
       let b = VerifierSteps.verify_epoch t aeh in
       intro_nout_bytes tsm (M.verify_step_model tsm le) out_bytes out_offset;
       if b
       then (
         rewrite (thread_state_inv t _)
                 (thread_state_inv t (M.verify_step_model tsm le));
         success t aeh out_offset out le 0ul;
         return (Some 0ul)
       )
       else (
         rewrite (thread_state_inv t _)
                 (thread_state_inv t tsm);
         fail t aeh out;
         return None
       )

     | _ ->
       match le with
       | AddM s s' r ->
         let b = VerifierSteps.vaddm t s s' r in
         verify_entry_cases t out_offset out aeh le b

       | AddB s ts tid r ->
         let b = VerifierSteps.vaddb t s ts tid r in
         verify_entry_cases t out_offset out aeh le b

       | EvictM pl ->
         VerifierSteps.vevictm t pl.s pl.s_;
         verify_entry_cases t out_offset out aeh le true

       | EvictB pl ->
         let b = VerifierSteps.vevictb t pl.s pl.t in
         verify_entry_cases t out_offset out aeh le b

       | EvictBM pl ->
         let b = VerifierSteps.vevictbm t pl.s pl.s_ pl.t in
         verify_entry_cases t out_offset out aeh le b

       | NextEpoch ->
         let b = VerifierSteps.nextepoch t in
         verify_entry_cases t out_offset out aeh le true

let verify_step_post (tsm:M.thread_state_model)
                     (t:thread_state_t) //handle to the thread state
                     (log_bytes:bytes)
                     (log_pos:U32.t{U32.v log_pos <= Seq.length log_bytes})
                     (out_bytes:bytes)
                     (out_offset:U32.t)
                     (out:A.array U8.t) //out array, to write outputs
                     (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
                     ([@@@smt_fallback] res:verify_result)
 : vprop
 = match res with
   | Parsing_failure _ ->
      pure (LogEntry.spec_parser_log_entry (Parser.bytes_from log_bytes log_pos) == None /\
            Parsing_failure?.log_pos res == log_pos) `star`
      thread_state_inv t tsm `star`
      TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false `star`
      array_pts_to out out_bytes

   | App_failure log_pos' ->
      thread_state_inv t tsm `star`
      TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false `star`
      array_pts_to out out_bytes

   | Verify_entry_failure _ ->
      pure (Verify_entry_failure?.log_pos res == log_pos) `star`
      exists_ (fun le ->
        pure (LogEntry.can_parse_log_entry log_bytes log_pos /\
              fst (LogEntry.spec_parse_log_entry log_bytes log_pos) == le) `star`
        verify_log_entry_post tsm t out_bytes out_offset out aeh le None)

   | Verify_success read wrote ->
      exists_ (fun le ->
        pure (LogEntry.maybe_parse_log_entry log_bytes log_pos == Some (le, U32.v read)) `star`
        verify_log_entry_post tsm t out_bytes out_offset out aeh le (Some wrote))

let intro_verify_step_post_parsing_failure
                     (#o:_)
                     (#tsm:M.thread_state_model)
                     (t:thread_state_t) //handle to the thread state
                     (log_bytes:erased bytes)
                     (log_pos:U32.t{U32.v log_pos <= Seq.length log_bytes})
                     (out_bytes:bytes)
                     (out_offset:U32.t)
                     (out:A.array U8.t) //out array, to write outputs
                     (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
  : STGhost unit o
    (thread_state_inv t tsm `star`
     TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false `star`
     array_pts_to out out_bytes)
    (fun _ ->
      verify_step_post tsm t log_bytes log_pos out_bytes out_offset out aeh (Parsing_failure log_pos))
    (requires
      LogEntry.spec_parser_log_entry (Parser.bytes_from log_bytes log_pos) == None)
    (ensures fun _ -> True)
  = intro_pure (LogEntry.spec_parser_log_entry (Parser.bytes_from log_bytes log_pos) == None /\
                Parsing_failure?.log_pos (Parsing_failure log_pos) == log_pos);
    rewrite (pure _ `star`
             thread_state_inv t tsm `star`
             TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false `star`
             array_pts_to out out_bytes)
             _

let intro_verify_step_post_app_failure
                     (#o:_)
                     (#tsm:M.thread_state_model)
                     (t:thread_state_t) //handle to the thread state
                     (log_bytes:erased bytes)
                     (log_pos:U32.t{U32.v log_pos <= Seq.length log_bytes})
                     (out_bytes:bytes)
                     (out_offset:U32.t)
                     (out:A.array U8.t)
                     (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
  : STGhostT unit o
    (thread_state_inv t tsm `star`
     TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false `star`
     array_pts_to out out_bytes)
    (fun _ ->
      verify_step_post tsm t log_bytes log_pos out_bytes out_offset out aeh (App_failure log_pos))
  = rewrite (thread_state_inv t tsm `star`
             TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false `star`
             array_pts_to out out_bytes)
             _

let intro_verify_step_post_verify_failure
                     (#o:_)
                     (#tsm:M.thread_state_model)
                     (t:thread_state_t) //handle to the thread state
                     (log_bytes:erased bytes)
                     (log_pos:U32.t{U32.v log_pos <= Seq.length log_bytes})
                     (out_bytes:bytes)
                     (out_offset:U32.t)
                     (out:A.array U8.t)
                     (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
                     (le: log_entry)
  : STGhost unit o
    (verify_log_entry_post tsm t out_bytes out_offset out aeh le None)
    (fun _ ->
      verify_step_post tsm t log_bytes log_pos out_bytes out_offset out aeh (Verify_entry_failure log_pos))
    (requires
       (match (LogEntry.spec_parser_log_entry (Parser.bytes_from log_bytes log_pos)) with
       | None -> False
       | Some (le', n') -> le == le'))
    (ensures fun _ -> True)
  = intro_pure (Verify_entry_failure?.log_pos (Verify_entry_failure log_pos) == log_pos);
    intro_pure (LogEntry.can_parse_log_entry log_bytes log_pos /\
                fst (LogEntry.spec_parse_log_entry log_bytes log_pos) == le);
    intro_exists le (fun le ->
      pure (LogEntry.can_parse_log_entry log_bytes log_pos /\
            fst (LogEntry.spec_parse_log_entry log_bytes log_pos) == le) `star`
      verify_log_entry_post tsm t out_bytes out_offset out aeh le None);
    rewrite_with (pure (Verify_entry_failure?.log_pos (Verify_entry_failure log_pos) == log_pos) `star`
             exists_ (fun le ->
               pure (LogEntry.can_parse_log_entry log_bytes log_pos /\
                     fst (LogEntry.spec_parse_log_entry log_bytes log_pos) == le) `star`
               verify_log_entry_post tsm t out_bytes out_offset out aeh le None))
            _
            (_ by FStar.Tactics.(trefl()))

let intro_verify_step_post_verify_success
                     (#o:_)
                     (#tsm:M.thread_state_model)
                     (t:thread_state_t) //handle to the thread state
                     (log_bytes:erased bytes)
                     (log_pos:U32.t{U32.v log_pos <= Seq.length log_bytes})
                     (out_bytes:bytes)
                     (out_offset:U32.t)
                     (out:A.array U8.t) //out array, to write outputs
                     (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
                     (le: log_entry)
                     (n_read:U32.t)
                     (n_written:U32.t)
  : STGhost unit o
    (verify_log_entry_post tsm t out_bytes out_offset out aeh le (Some n_written))
    (fun _ ->
      verify_step_post tsm t log_bytes log_pos out_bytes out_offset out aeh (Verify_success n_read n_written))
    (requires
       LogEntry.can_parse_log_entry log_bytes log_pos /\
       LogEntry.spec_parse_log_entry log_bytes log_pos == (le, U32.v n_read))
    (ensures fun _ -> True)
  = intro_pure (LogEntry.maybe_parse_log_entry log_bytes log_pos == Some (le, U32.v n_read));
    intro_exists le (fun le ->
      pure (LogEntry.maybe_parse_log_entry log_bytes log_pos == Some (le, U32.v n_read)) `star`
      verify_log_entry_post tsm t out_bytes out_offset out aeh le (Some n_written))

let intro_verify_step_post_runapp_success
                     (#o:_)
                     (#tsm:M.thread_state_model)
                     (t:thread_state_t) //handle to the thread state
                     (log_bytes:erased bytes)
                     (log_pos:U32.t{U32.v log_pos <= Seq.length log_bytes})
                     (pl: runApp_payload)
                     (out_bytes:bytes)
                     (out_offset:U32.t)
                     (out:A.array U8.t)
                     (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
                     (n_read:U32.t)
                     (n_written:U32.t)
                     (res:Application.verify_runapp_result)
  : STGhost unit o
    (Application.verify_runapp_entry_post tsm t pl out_bytes out_offset out res `star`
     TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false)
    (fun _ ->
      verify_step_post tsm t log_bytes log_pos out_bytes out_offset out aeh (Verify_success n_read n_written))
    (requires
      res == Application.Run_app_success n_written /\ not tsm.failed /\
      LogEntry.can_parse_log_entry log_bytes log_pos /\
      LogEntry.spec_parse_log_entry log_bytes log_pos == (RunApp pl, U32.v n_read))
    (ensures fun _ -> True)
  = rewrite (Application.verify_runapp_entry_post tsm t pl out_bytes out_offset out res)
            (Application.verify_runapp_entry_post tsm t pl out_bytes out_offset out (Application.Run_app_success n_written));
    let out_bytes' = elim_exists () in
    assert_ (thread_state_inv t (M.verify_step_model tsm (RunApp pl)));
    assert_ (array_pts_to out out_bytes');
    compat_with_any_anchor_of_le tsm.processed_entries (RunApp pl);
    TLM.update_tid_log aeh.mlogs tsm.thread_id tsm.processed_entries (M.verify_step_model tsm (RunApp pl)).processed_entries;
    success t aeh out_offset out (RunApp pl) n_written;
    assert_ (verify_log_entry_post tsm t out_bytes out_offset out aeh (RunApp pl) (Some n_written));
    intro_verify_step_post_verify_success t log_bytes log_pos out_bytes out_offset out aeh (RunApp pl) n_read n_written

val verify_step (#tsm:M.thread_state_model)
                (t:thread_state_t) //handle to the thread state
                (#log_perm:perm)
                (#log_bytes:erased bytes)
                (#len:U32.t)
                (log_pos:U32.t{U32.v log_pos <= Seq.length log_bytes})
                (log:larray U8.t len) //concrete log
                (#outlen:U32.t)
                (#out_bytes:erased bytes)
                (out_offset:U32.t{ U32.v out_offset <= Seq.length out_bytes })
                (out:larray U8.t outlen) //out array, to write outputs
                (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
  : ST verify_result
    (//precondition
      A.pts_to log log_perm log_bytes `star` //the log contains log_bytes
      thread_state_inv t tsm `star` //thread state is initially tsm
      array_pts_to out out_bytes `star` //we have permission to out, don't care what it contains
      TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false //and the global state contains this thread's entries
    )
    (fun res -> //postcondition
      A.pts_to log log_perm log_bytes `star` //log contents didn't change
      verify_step_post tsm t log_bytes log_pos out_bytes out_offset out aeh res)
    (requires not tsm.failed)
    (ensures fun _ -> True)

#push-options "--ifuel 2" // for spec_parser

let verify_step (#tsm:M.thread_state_model)
                (t:thread_state_t) //handle to the thread state
                (#log_perm:perm)
                (#log_bytes:erased bytes)
                (#len:U32.t)
                (log_pos:U32.t{U32.v log_pos <= Seq.length log_bytes})
                (log:larray U8.t len) //concrete log
                (#out_len:U32.t)
                (#out_bytes:erased bytes)
                (out_offset:U32.t{U32.v out_offset <= Seq.length out_bytes})
                (out:larray U8.t out_len) //out array, to write outputs
                (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
    = A.pts_to_length log _;
      A.pts_to_length out _;
      let res = LogEntry.parser_log_entry len log_pos U32.(len -^ log_pos) log in
      match res with
      | None ->
        intro_verify_step_post_parsing_failure t log_bytes log_pos out_bytes out_offset out aeh;
        return (Parsing_failure log_pos)

      | Some (le, read) ->
        match le with
        | RunApp pl ->
          let app_res =
            let s = Ghost.hide (Zeta.Steel.Parser.slice log_bytes log_pos U32.(len -^ log_pos)) in
            let pl_pos0 = Zeta.Steel.LogEntry.runapp_payload_offset le s in
            let pl_pos = log_pos `U32.add` pl_pos0 in
            Application.run_app_function
              len pl pl_pos log
              out_len out_offset out
              t
              // VerifierTypes.read_store
              // VerifierTypes.write_store
          in
          // assert_ (Application.verify_runapp_entry_post tsm t pl out_bytes out_offset out app_res);
          begin
          match app_res with
          | Application.Run_app_parsing_failure
          | Application.Run_app_verify_failure ->
            rewrite (Application.verify_runapp_entry_post tsm t pl out_bytes out_offset out app_res)
                    (thread_state_inv t tsm `star`
                     array_pts_to out out_bytes);
            intro_verify_step_post_app_failure t log_bytes log_pos out_bytes out_offset out aeh;
            return (App_failure log_pos)

          | Application.Run_app_success written ->
            let _ = intro_verify_step_post_runapp_success
                        t log_bytes log_pos pl
                        out_bytes out_offset out aeh read written app_res in
            return (Verify_success read written)
          end

        | _ ->
          let b = verify_log_entry t out_offset out aeh le in
          match b with
          | None ->
            rewrite (verify_log_entry_post tsm t out_bytes out_offset out aeh le b)
                    (verify_log_entry_post tsm t out_bytes out_offset out aeh le None);
            intro_verify_step_post_verify_failure t log_bytes log_pos out_bytes out_offset out aeh le;
            return (Verify_entry_failure log_pos)

          | Some written ->
            rewrite (verify_log_entry_post tsm t out_bytes out_offset out aeh le b)
                    (verify_log_entry_post tsm t out_bytes out_offset out aeh le (Some written));
            intro_verify_step_post_verify_success t log_bytes log_pos out_bytes out_offset out aeh le read written;
            return (Verify_success read written)


////////////////////////////////////////////////////////////////////////////////

let elim_verify_step_post_parsing_failure
                     #o
                     (#tsm:M.thread_state_model)
                     (#t:thread_state_t) //handle to the thread state
                     (#log_bytes:bytes)
                     (#log_pos:U32.t{U32.v log_pos <= Seq.length log_bytes})
                     (#out_bytes:bytes)
                     (#out_offset:U32.t)
                     (#out:A.array U8.t) //out array, to write outputs
                     (#aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
                     (loc:U32.t)
   : STGhost unit o
     (verify_step_post tsm t log_bytes log_pos out_bytes out_offset out aeh (Parsing_failure loc))
     (fun _ ->
        thread_state_inv t tsm `star`
        TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false `star`
        array_pts_to out out_bytes)
     (requires True)
     (ensures fun _ ->
       LogEntry.spec_parser_log_entry (Parser.bytes_from log_bytes log_pos) == None /\
       loc == log_pos)
   = rewrite
        (verify_step_post tsm t log_bytes log_pos out_bytes out_offset out aeh (Parsing_failure loc))
        (pure (LogEntry.spec_parser_log_entry (Parser.bytes_from log_bytes log_pos) == None /\
               loc == log_pos) `star`
         thread_state_inv t tsm `star`
         TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false `star`
         array_pts_to out out_bytes);
     elim_pure _


let intro_some_failure #o (#tsm:M.thread_state_model)
                       (t:thread_state_t) //handle to the thread state
                       (#out_bytes:_)
                       (out:A.array U8.t)
                       (#entries:_)
                       (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
  : STGhostT unit o
    (thread_state_inv t tsm `star`
     TLM.tid_pts_to aeh.mlogs tsm.thread_id full entries false `star`
     array_pts_to out out_bytes)
    (fun _ -> some_failure t out aeh)
  = VerifierTypes.extract_tsm_entries_invariant t;
    intro_exists tsm (thread_state_inv t);
    rewrite (TLM.tid_pts_to aeh.mlogs tsm.thread_id full entries false)
            (TLM.tid_pts_to aeh.mlogs (VerifierTypes.thread_id t) full entries false);
    intro_exists entries (fun entries -> TLM.tid_pts_to aeh.mlogs (VerifierTypes.thread_id t) full entries false);
    intro_exists out_bytes (array_pts_to out);
    rewrite (exists_ (thread_state_inv t) `star`
             exists_ (fun entries -> TLM.tid_pts_to aeh.mlogs (VerifierTypes.thread_id t) full entries false) `star`
             exists_ (array_pts_to out))
            (some_failure t out aeh);
    ()


let elim_verify_step_post_app_failure
                     #o
                     (#tsm:M.thread_state_model)
                     (#t:thread_state_t) //handle to the thread state
                     (#log_bytes:bytes)
                     (#log_pos:U32.t{U32.v log_pos <= Seq.length log_bytes})
                     (#out_bytes:bytes)
                     (#out_offset:U32.t)
                     (#out:A.array U8.t) //out array, to write outputs
                     (#aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
                     (res:U32.t)
   : STGhostT unit o
     (verify_step_post tsm t log_bytes log_pos out_bytes out_offset out aeh (App_failure res))
     (fun _ -> some_failure t out aeh)
   = rewrite
        (verify_step_post tsm t log_bytes log_pos out_bytes out_offset out aeh (App_failure res))
        (thread_state_inv t tsm `star`
         TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false `star`
         array_pts_to out out_bytes);
     intro_some_failure t out aeh

let elim_verify_step_post_log_entry_failure
                     #o
                     (#tsm:M.thread_state_model)
                     (#t:thread_state_t) //handle to the thread state
                     (#log_bytes:bytes)
                     (#log_pos:U32.t{U32.v log_pos <= Seq.length log_bytes})
                     (#out_bytes:bytes)
                     (#out_offset:U32.t)
                     (#out:A.array U8.t) //out array, to write outputs
                     (#aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
                     (res:U32.t)
   : STGhostT unit o
     (verify_step_post tsm t log_bytes log_pos out_bytes out_offset out aeh (Verify_entry_failure res))
     (fun _ -> some_failure t out aeh)
   = rewrite_with
        (verify_step_post tsm t log_bytes log_pos out_bytes out_offset out aeh (Verify_entry_failure res))
        (pure (Verify_entry_failure?.log_pos (Verify_entry_failure res) == log_pos) `star`
          exists_ (fun le ->
            pure (LogEntry.can_parse_log_entry log_bytes log_pos /\
                  fst (LogEntry.spec_parse_log_entry log_bytes log_pos) == le) `star`
            verify_log_entry_post tsm t out_bytes out_offset out aeh le None))
        (_ by FStar.Tactics.(
            norm [delta_only [`%verify_step_post]; iota];
            trefl()));
     elim_pure _;
     let le = elim_exists () in
     elim_pure _;
     rewrite (verify_log_entry_post tsm t out_bytes out_offset out aeh le None)
             (some_failure t out aeh)

#push-options "--ifuel 1 --z3rlimit_factor 5"
#restart-solver

let n_out_bytes_trans (tsm tsm1 tsm2:M.thread_state_model) le init nout1 nout2 out_bytes out_bytes_1 out_bytes_2
  : Lemma
    (requires
      Seq.length tsm.app_results <= Seq.length tsm1.app_results /\
      not tsm.failed /\
      not tsm1.failed /\
      tsm2 == M.verify_step_model tsm1 le /\
      UInt.fits (U32.v init + U32.v nout1) 32 /\
      UInt.fits (U32.v nout1 + U32.v nout2) 32 /\
      Application.n_out_bytes tsm tsm1 init nout1 out_bytes out_bytes_1 /\
      Application.n_out_bytes tsm1 tsm2 U32.(init +^ nout1) nout2 out_bytes_1 out_bytes_2)
    (ensures
      Application.n_out_bytes tsm tsm2 init U32.(nout1 +^ nout2) out_bytes out_bytes_2)
  = M.delta_out_bytes_trans tsm tsm1 le;
    assert (M.delta_out_bytes tsm tsm2 ==
            Seq.append (M.delta_out_bytes tsm tsm1)
                       (M.delta_out_bytes tsm1 tsm2));
    assert (Seq.length out_bytes == Seq.length out_bytes_2);
    assert (U32.v init <= Seq.length out_bytes);
    assert (U32.v nout1 + U32.v nout2 <= Seq.length out_bytes - U32.v init);
    let nout = U32.(nout1 +^ nout2) in
    let pfx, _, sfx = Application.split3 out_bytes init nout in
    let pfx', s, sfx' = Application.split3 out_bytes_2 init nout in
    let _ =
      calc (==) {
        pfx;
      (==) {}
       Seq.slice out_bytes 0 (U32.v init);
      (==) { }
       Seq.slice out_bytes_1 0 (U32.v init);
      (Seq.equal) { Seq.Properties.slice_slice out_bytes_1 0 (U32.v init + U32.v nout1) 0 (U32.v init) }
       Seq.slice (Seq.slice out_bytes_1 0 (U32.v init + U32.v nout1)) 0 (U32.v init);
      (Seq.equal) { }
       Seq.slice (Seq.slice out_bytes_2 0 (U32.v init + U32.v nout1)) 0 (U32.v init);
      (Seq.equal) {Seq.Properties.slice_slice out_bytes_2 0 (U32.v init + U32.v nout1) 0 (U32.v init) }
       Seq.slice out_bytes_2 0 (U32.v init);
      (Seq.equal) {}
        pfx';
      }
    in
    let endpos = U32.v init + U32.v nout in
    let len = Seq.length out_bytes in
    let _ =
      calc (==) {
        sfx';
      (==) {}
       Seq.slice out_bytes_2 endpos len;
      (==) {}
       Seq.slice out_bytes_1 endpos len;
      (==) { Seq.Properties.slice_slice out_bytes_1 (U32.v init + U32.v nout1) len
                                                  (U32.v nout2) (len - (U32.v init + U32.v nout1)) }
       Seq.slice (Seq.slice out_bytes_1 (U32.v init + U32.v nout1) len)
                 (U32.v nout2) (len - (U32.v init + U32.v nout1));
      (==) { }
       Seq.slice (Seq.slice out_bytes (U32.v init + U32.v nout1) len)
                 (U32.v nout2) (len - (U32.v init + U32.v nout1));
      (==) { Seq.Properties.slice_slice out_bytes (U32.v init + U32.v nout1) len
                                                  (U32.v nout2) (len - (U32.v init + U32.v nout1)) }
        sfx;
      }
    in
    let _ =
      calc (==) {
        s;
      (==) {}
        Seq.slice out_bytes_2 (U32.v init) (U32.v init + U32.v nout);
      (Seq.equal) {}
        Seq.append (Seq.slice out_bytes_2 (U32.v init) (U32.v init + U32.v nout1))
                   (Seq.slice out_bytes_2 (U32.v init + U32.v nout1) (U32.v init + U32.v nout));
      (==) {}
        Seq.append (Seq.slice out_bytes_2 (U32.v init) (U32.v init + U32.v nout1))
                   (M.delta_out_bytes tsm1 tsm2);
      (==) {
                  calc (==) {
                      Seq.slice out_bytes_2 (U32.v init) (U32.v init + U32.v nout1);
                   (==) { Seq.slice_slice out_bytes_2 0 (U32.v init + U32.v nout1) (U32.v init) (U32.v init + U32.v nout1) }
                      Seq.slice (Seq.slice out_bytes_2 0 (U32.v init + U32.v nout1))
                                (U32.v init) (U32.v init + U32.v nout1);
                   (==) {}
                      Seq.slice (Seq.slice out_bytes_1 0 (U32.v init + U32.v nout1))
                                (U32.v init) (U32.v init + U32.v nout1);
                   (==) { Seq.slice_slice out_bytes_1 0 (U32.v init + U32.v nout1) (U32.v init) (U32.v init + U32.v nout1) }
                      Seq.slice out_bytes_1 (U32.v init) (U32.v init + U32.v nout1);
                  }
           }
        Seq.append (Seq.slice out_bytes_1 (U32.v init) (U32.v init + U32.v nout1))
                   (M.delta_out_bytes tsm1 tsm2);
    } in
    if tsm2.failed
    then ()
    else assert (s `Seq.equal` M.delta_out_bytes tsm tsm2)

#restart-solver

let stitch_verify_post_step
                   (#o:_)
                   (#tsm:M.thread_state_model)
                   (#t:thread_state_t) //handle to the thread state
                   (#log_bytes:bytes)
                   (log_pos:U32.t { U32.v log_pos <= Seq.length log_bytes })
                   (out_bytes:bytes)
                   (out_pos:U32.t)
                   (#out:A.array U8.t)
                   (#aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
                   (#les:M.log)
                   (#out_bytes_1:bytes)
                   (log_pos':U32.t)
                   (out_pos':U32.t {
                      UInt.fits (Seq.length log_bytes) 32 /\
                      UInt.fits (Seq.length out_bytes) 32
                    })
  : STGhost (squash ((U32.v log_pos + U32.v log_pos') <= Seq.length log_bytes /\
                     (U32.v out_pos + U32.v out_pos') <= Seq.length out_bytes /\
                     UInt.fits (Seq.length log_bytes) 32 /\
                     UInt.fits (Seq.length out_bytes) 32)) o
    (verify_step_post (M.verify_model tsm les) t
                      log_bytes log_pos
                      out_bytes_1 out_pos out
                      aeh (Verify_success log_pos' out_pos'))
    (fun _ ->
      verify_post tsm t log_bytes out_bytes out aeh
        (Verify_success U32.(log_pos +^ log_pos') U32.(out_pos +^ out_pos')))
    (requires
      Log.parse_log_up_to log_bytes (U32.v log_pos) == Some les /\
      Application.n_out_bytes tsm (M.verify_model tsm les) 0ul out_pos out_bytes out_bytes_1 /\
      not (M.verify_model tsm les).failed)
    (ensures fun _ ->
      True)
  = let le = elim_exists () in
    elim_pure _;
    let out_bytes_2 = elim_exists () in
    elim_pure _;
    assert_ (array_pts_to out out_bytes_2);
    let tsm1 = M.verify_model tsm les in
    let tsm2 = M.verify_step_model tsm1 le in
    let les' = Seq.snoc les le in
    M.verify_model_snoc tsm les le;
    assert (tsm2 == M.verify_model tsm les');
    rewrite (thread_state_inv t _)
            (thread_state_inv t (M.verify_model tsm les'));
    assert (tsm1.thread_id == tsm2.thread_id);
    rewrite (TLM.tid_pts_to _ _ _ _ _)
            (TLM.tid_pts_to aeh.mlogs
                            (M.verify_model tsm les').thread_id
                            full
                            (M.verify_model tsm les').processed_entries
                            false);
    assert (Application.n_out_bytes tsm1 tsm2 out_pos out_pos' out_bytes_1 out_bytes_2);
    // M.delta_out_bytes_trans tsm tsm1 le;
    // assert (M.delta_out_bytes tsm tsm2 ==
    //         Seq.append (M.delta_out_bytes tsm tsm1)
    //                    (M.delta_out_bytes tsm1 tsm2));
    // assert (Seq.length out_bytes == Seq.length out_bytes_2);
    // assert (U32.v (U32.(out_pos +^ out_pos')) <=
    //            Seq.length out_bytes);
    M.not_failed_pre_steps tsm les;
    M.app_results_monotone tsm les;
    n_out_bytes_trans tsm tsm1 tsm2 le 0ul out_pos out_pos' out_bytes out_bytes_1 out_bytes_2;
    intro_pure (Application.n_out_bytes
                      tsm (M.verify_model tsm les')
                      0ul U32.(out_pos +^ out_pos')
                      out_bytes
                      out_bytes_2);
    intro_exists_erased out_bytes_2 (fun out_bytes_2 ->
      array_pts_to out out_bytes_2 `star`
      pure (Application.n_out_bytes
                  tsm (M.verify_model tsm les')
                  0ul U32.(out_pos +^ out_pos')
                  out_bytes out_bytes_2));
    rewrite_with
      (exists_ (fun out_bytes_2 ->
        array_pts_to out out_bytes_2 `star`
        pure (Application.n_out_bytes
                  tsm (M.verify_model tsm les')
                  0ul U32.(out_pos +^ out_pos')
                  out_bytes out_bytes_2)))
      (verify_post_out_bytes tsm out_bytes U32.(out_pos +^ out_pos') out les')
      (_ by FStar.Tactics.(
        norm [delta_only [`%verify_post_out_bytes]];
        trefl())
      );
    assert (LogEntry.maybe_parse_log_entry log_bytes log_pos == Some (reveal le, U32.v log_pos'));
    Log.parse_log_up_to_trans log_bytes (U32.v log_pos) les;
    intro_pure (Log.parse_log_up_to log_bytes (U32.v (U32.(log_pos +^ log_pos'))) == Some les');
    intro_exists les' (fun les' ->
      pure (Log.parse_log_up_to log_bytes (U32.v (U32.(log_pos +^ log_pos'))) == Some les') `star`
      thread_state_inv t (M.verify_model tsm les') `star`
      TLM.tid_pts_to aeh.mlogs
                      (M.verify_model tsm les').thread_id
                      full
                      (M.verify_model tsm les').processed_entries
                      false `star`
      verify_post_out_bytes tsm out_bytes U32.(out_pos +^ out_pos') out les');
     rewrite_with
       (exists_ _)
       (verify_post tsm t log_bytes out_bytes out aeh
         (Verify_success U32.(log_pos +^ log_pos') U32.(out_pos +^ out_pos')))
       (_ by FStar.Tactics.(
         norm [delta_only [`%verify_post]; iota];
         trefl())
       );
     ()

#pop-options

#pop-options

type seq_index (s:Ghost.erased bytes) =
  i:U32.t{U32.v i <= Seq.length s}

let inv_pure_pred
  (len:U32.t)
  (#log_bytes:erased bytes)
  (#out_bytes:erased bytes)
  (b:bool)
  (res:verify_result)
  (log_pos:seq_index log_bytes)
  (out_pos:seq_index out_bytes)
  : prop
  = (Verify_success? res ==> res == Verify_success log_pos out_pos) /\
    (b <==> (Verify_success? res /\ U32.v log_pos < U32.v len))

[@@ __reduce__]
let inv_local_refs (tsm:M.thread_state_model)
  (t:thread_state_t) //handle to the thread state
  (log_bytes:erased bytes)
  (len:U32.t)
  (outlen:U32.t)
  (out_bytes:erased bytes)
  (out:larray U8.t outlen) //out array, to write outputs
  (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
  (r_log_pos:R.ref (seq_index log_bytes))
  (r_out_pos:R.ref (seq_index out_bytes))
  (r_res:R.ref verify_result)
  (b:bool)
  (log_pos:seq_index log_bytes)
  (res:verify_result)
  (out_pos:seq_index out_bytes)
  : vprop
  = verify_post tsm t log_bytes out_bytes out aeh res
      `star`
    pure (inv_pure_pred len b res log_pos out_pos)

[@@ __reduce__]
let inv_out_pos (tsm:M.thread_state_model)
  (t:thread_state_t) //handle to the thread state
  (log_bytes:erased bytes)
  (len:U32.t)
  (outlen:U32.t)
  (out_bytes:erased bytes)
  (out:larray U8.t outlen) //out array, to write outputs
  (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
  (r_log_pos:R.ref (seq_index log_bytes))
  (r_out_pos:R.ref (seq_index out_bytes))
  (r_res:R.ref verify_result)
  (b:bool)
  (log_pos:seq_index log_bytes)
  (res:verify_result)
  : vprop
  = exists_ (fun out_pos ->
             R.pts_to r_out_pos full_perm out_pos
               `star`
             inv_local_refs tsm t log_bytes len outlen out_bytes out aeh r_log_pos r_out_pos r_res b log_pos res out_pos)

#set-options "--print_implicits"

[@@ __reduce__]
let inv_res (tsm:M.thread_state_model)
  (t:thread_state_t) //handle to the thread state
  (log_bytes:erased bytes)
  (len:U32.t)
  (outlen:U32.t)
  (out_bytes:erased bytes)
  (out:larray U8.t outlen) //out array, to write outputs
  (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
  (r_log_pos:R.ref (seq_index log_bytes))
  (r_out_pos:R.ref (seq_index out_bytes))
  (r_res:R.ref verify_result)
  (b:bool)
  (log_pos:seq_index log_bytes)
  : vprop
  = exists_ (fun res ->
             R.pts_to r_res full_perm res
               `star`
             inv_out_pos tsm t log_bytes len outlen out_bytes out aeh r_log_pos r_out_pos r_res b log_pos res)

[@@ __reduce__]
let inv_log_pos (tsm:M.thread_state_model)
  (t:thread_state_t) //handle to the thread state
  (log_bytes:erased bytes)
  (len:U32.t)
  (outlen:U32.t)
  (out_bytes:erased bytes)
  (out:larray U8.t outlen) //out array, to write outputs
  (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
  (r_log_pos:R.ref (seq_index log_bytes))
  (r_out_pos:R.ref (seq_index out_bytes))
  (r_res:R.ref verify_result)
  (b:bool)
  : vprop
  = exists_ (fun log_pos ->
             R.pts_to r_log_pos full_perm log_pos
               `star`
             inv_res tsm t log_bytes len outlen out_bytes out aeh r_log_pos r_out_pos r_res b log_pos)

[@@ __reduce__]
let inv (tsm:M.thread_state_model)
  (t:thread_state_t) //handle to the thread state
  (log_perm:perm)
  (log_bytes:erased bytes)
  (len:U32.t)
  (log:larray U8.t len) //concrete log
  (outlen:U32.t)
  (out_bytes:erased bytes)
  (out:larray U8.t outlen) //out array, to write outputs
  (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
  (r_log_pos:R.ref (seq_index log_bytes))
  (r_out_pos:R.ref (seq_index out_bytes))
  (r_res:R.ref verify_result)
  : bool -> vprop
  = fun b ->
    A.pts_to log log_perm log_bytes
      `star`
    inv_log_pos tsm t log_bytes len outlen out_bytes out aeh r_log_pos r_out_pos r_res b

let elim_inv_false (tsm:M.thread_state_model)
  (t:thread_state_t) //handle to the thread state
  (log_perm:perm)
  (log_bytes:erased bytes)
  (len:U32.t)
  (log:larray U8.t len) //concrete log
  (outlen:U32.t)
  (out_bytes:erased bytes)
  (out:larray U8.t outlen) //out array, to write outputs
  (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
  (r_log_pos:R.ref (seq_index log_bytes))
  (r_res:R.ref verify_result)
  (r_out_pos:R.ref (seq_index out_bytes))
  : ST verify_result
       (inv tsm t log_perm log_bytes len log outlen out_bytes out aeh r_log_pos r_out_pos r_res false)
       (fun res ->
        A.pts_to log log_perm log_bytes
          `star`
        verify_post tsm t log_bytes out_bytes out aeh res)
       (requires True)
       (ensures fun res -> verify_result_complete len res)
  = A.pts_to_length log _;
    let _ = elim_exists () in
    let _ = elim_exists () in
    let _ = elim_exists () in
    elim_pure (inv_pure_pred _ _ _ _ _);
    let res = R.read r_res in
    R.free r_log_pos;
    R.free r_res;
    R.free r_out_pos;
    return res
       
let init_inv (tsm:M.thread_state_model)
  (t:thread_state_t) //handle to the thread state
  (log_perm:perm)
  (log_bytes:erased bytes)
  (len:U32.t)
  (log:larray U8.t len) //concrete log
  (outlen:U32.t)
  (out_bytes:erased bytes)
  (out:larray U8.t outlen) //out array, to write outputs
  (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
  (r_log_pos:R.ref (seq_index log_bytes))
  (r_out_pos:R.ref (seq_index out_bytes))
  (r_res:R.ref verify_result)
  (log_pos:seq_index log_bytes)
  (out_pos:seq_index out_bytes)
  : STT unit
      (A.pts_to log log_perm log_bytes
         `star`
       verify_post tsm t log_bytes out_bytes out aeh (Verify_success log_pos out_pos)
         `star`
       R.pts_to r_log_pos full_perm 0ul
         `star`
       R.pts_to r_out_pos full_perm 0ul
         `star`
       R.pts_to r_res full_perm (Verify_success 0ul 0ul))
      (fun _ -> exists_ (inv tsm t log_perm log_bytes len log outlen out_bytes out aeh r_log_pos r_out_pos r_res))
  = A.pts_to_length log _;
    R.write r_log_pos log_pos;
    let res = Verify_success log_pos out_pos in
    R.write r_res res;
    R.write r_out_pos out_pos;
    let b = U32.(log_pos <^ len) in
    intro_pure _;
    intro_exists out_pos (fun out_pos ->
                          R.pts_to r_out_pos full_perm out_pos
                            `star`
                          inv_local_refs tsm t log_bytes len outlen out_bytes out aeh r_log_pos r_out_pos r_res b log_pos res out_pos);
    intro_exists res
                 (fun res ->
                  R.pts_to r_res full_perm res
                    `star`
                  inv_out_pos tsm t log_bytes len outlen out_bytes out aeh r_log_pos r_out_pos r_res b log_pos res);
    intro_exists log_pos
                 (fun log_pos ->
                  R.pts_to r_log_pos full_perm log_pos
                    `star`
                  inv_res tsm t log_bytes len outlen out_bytes out aeh r_log_pos r_out_pos r_res b log_pos);
    intro_exists b (inv tsm t log_perm log_bytes len log outlen out_bytes out aeh r_log_pos r_out_pos r_res)

let intro_inv_body (#opened:_)
  (tsm:M.thread_state_model)
  (t:thread_state_t) //handle to the thread state
  (log_perm:perm)
  (log_bytes:erased bytes)
  (len:U32.t)
  (log:larray U8.t len) //concrete log
  (outlen:U32.t)
  (out_bytes:erased bytes)
  (out:larray U8.t outlen) //out array, to write outputs
  (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
  (r_log_pos:R.ref (seq_index log_bytes))
  (r_out_pos:R.ref (seq_index out_bytes))
  (r_res:R.ref verify_result)
  (log_pos:seq_index log_bytes)
  (res:verify_result)
  (out_pos:seq_index out_bytes)
  : STGhost unit opened
      (A.pts_to log log_perm log_bytes
         `star`
       verify_post tsm t log_bytes out_bytes out aeh res
         `star`
       R.pts_to r_log_pos full_perm log_pos
         `star`
       R.pts_to r_res full_perm res
         `star`
       R.pts_to r_out_pos full_perm out_pos)
      (fun _ -> exists_ (inv tsm t log_perm log_bytes len log outlen out_bytes out aeh r_log_pos r_out_pos r_res))
      (requires Verify_success? res ==> res == Verify_success log_pos out_pos)
      (ensures fun _ -> True)
  = A.pts_to_length log _;
    let b = Verify_success? res && U32.(log_pos <^ len) in
    intro_pure _;
    intro_exists out_pos (fun out_pos ->
                          R.pts_to r_out_pos full_perm out_pos
                            `star`
                          inv_local_refs tsm t log_bytes len outlen out_bytes out aeh r_log_pos r_out_pos r_res b log_pos res out_pos);
    intro_exists res
                 (fun res ->
                  R.pts_to r_res full_perm res
                    `star`
                  inv_out_pos tsm t log_bytes len outlen out_bytes out aeh r_log_pos r_out_pos r_res b log_pos res);
    intro_exists log_pos
                 (fun log_pos ->
                  R.pts_to r_log_pos full_perm log_pos
                    `star`
                  inv_res tsm t log_bytes len outlen out_bytes out aeh r_log_pos r_out_pos r_res b log_pos);
    intro_exists b (inv tsm t log_perm log_bytes len log outlen out_bytes out aeh r_log_pos r_out_pos r_res)

let verify_log_loop_body (tsm:M.thread_state_model)
  (t:thread_state_t) //handle to the thread state
  (log_perm:perm)
  (log_bytes:erased bytes)
  (len:U32.t)
  (log:larray U8.t len) //concrete log
  (outlen:U32.t)
  (out_bytes:erased bytes)
  (out:larray U8.t outlen) //out array, to write outputs
  (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
  (r_log_pos:R.ref (seq_index log_bytes))
  (r_out_pos:R.ref (seq_index out_bytes))
  (r_res:R.ref verify_result)
  ()
  : STT unit
    (inv tsm t log_perm log_bytes len log outlen out_bytes out aeh r_log_pos r_out_pos r_res true)
    (fun res ->
     exists_ (inv tsm t log_perm log_bytes len log outlen out_bytes out aeh r_log_pos r_out_pos r_res))
  = A.pts_to_length log _;
    let g_log_pos = elim_exists () in  //log_pos
    let g_res_prev = elim_exists () in  //res
    let g_out_pos = elim_exists () in  //out_pos
    elim_pure _;

    let log_pos = R.read r_log_pos in
    let out_pos = R.read r_out_pos in
    let res_prev = R.read r_res in

    rewrite
      (verify_post tsm t log_bytes out_bytes out aeh res_prev)
      (verify_post tsm t log_bytes out_bytes out aeh (Verify_success log_pos out_pos));

    let _log = elim_exists () in
    let _out_bytes_1 = elim_exists () in
    elim_pure _;
    elim_pure _;
    A.pts_to_length out _;
    let is_failed = VerifierSteps.check_failed t in
    if is_failed
    then (
      intro_some_failure t out aeh;
      let res = Verify_entry_failure log_pos in
      intro_pure (Parsing_failure? res ==>
                  ~ (LogEntry.can_parse_log_entry log_bytes (Parsing_failure?.log_pos res)));
      rewrite (some_failure t out aeh `star` pure _)
              (verify_post tsm t log_bytes out_bytes out aeh res);
      R.write r_res res;
      intro_inv_body tsm t log_perm log_bytes len log outlen out_bytes out aeh r_log_pos r_out_pos r_res log_pos res out_pos
     ) else (
       assert (not (M.verify_model tsm _log).failed);
       let res = verify_step t log_pos log out_pos out aeh in
       assert_ (verify_step_post (M.verify_model tsm _log) t log_bytes log_pos _out_bytes_1 out_pos out aeh res);
       match res
         returns STT unit
                     (A.pts_to log log_perm log_bytes
                        `star`
                      verify_step_post (M.verify_model tsm _log) t log_bytes log_pos _out_bytes_1 out_pos out aeh res
                        `star`
                      R.pts_to r_log_pos full_perm log_pos
                        `star`
                      R.pts_to r_res full_perm res_prev
                        `star`
                      R.pts_to r_out_pos full_perm out_pos)
                     (fun _ -> exists_ (inv tsm t log_perm log_bytes len log outlen out_bytes out aeh r_log_pos r_out_pos r_res))
       with
       | Parsing_failure loc ->
         elim_verify_step_post_parsing_failure loc;
         intro_some_failure t out aeh;
         let res' = Parsing_failure loc in
         intro_pure (Parsing_failure? res' ==>
                     ~ (LogEntry.can_parse_log_entry log_bytes (Parsing_failure?.log_pos res')));
         rewrite (some_failure t out aeh `star` pure _)
                 (verify_post tsm t log_bytes out_bytes out aeh res');
         R.write r_res res';
         intro_inv_body tsm t log_perm log_bytes len log outlen out_bytes out aeh r_log_pos r_out_pos r_res log_pos res out_pos

       | App_failure loc ->
         elim_verify_step_post_app_failure loc;
         let res' = App_failure loc in
         intro_pure (Parsing_failure? res' ==>
                     ~ (LogEntry.can_parse_log_entry log_bytes (Parsing_failure?.log_pos res')));
         rewrite (some_failure t out aeh `star` pure _)
                 (verify_post tsm t log_bytes out_bytes out aeh res');
         R.write r_res res';
         intro_inv_body tsm t log_perm log_bytes len log outlen out_bytes out aeh r_log_pos r_out_pos r_res log_pos res out_pos

       | Verify_entry_failure loc ->
         elim_verify_step_post_log_entry_failure loc;
         let res' = res in
         intro_pure (Parsing_failure? res' ==>
                     ~ (LogEntry.can_parse_log_entry log_bytes (Parsing_failure?.log_pos res')));
         rewrite (some_failure t out aeh `star` pure _)
                 (verify_post tsm t log_bytes out_bytes out aeh res');
         R.write r_res res';
         intro_inv_body tsm t log_perm log_bytes len log outlen out_bytes out aeh r_log_pos r_out_pos r_res log_pos res out_pos

       | Verify_success read wrote ->
         let _ = stitch_verify_post_step #_ #tsm #t
           #(Ghost.reveal log_bytes) log_pos out_bytes out_pos #_ #_ #_ #_ read wrote in
         let res' = Verify_success U32.(log_pos +^ read) U32.(out_pos +^ wrote) in
         let log_pos = U32.(log_pos +^ read) in
         let out_pos = U32.(out_pos +^ wrote) in
         R.write r_res res';
         R.write r_log_pos log_pos;
         R.write r_out_pos out_pos;
         intro_inv_body tsm t log_perm log_bytes len log outlen out_bytes out aeh r_log_pos r_out_pos r_res log_pos res' out_pos
       )

let verify_log_loop_cond
  (tsm:M.thread_state_model)
  (t:thread_state_t) //handle to the thread state
  (log_perm:perm)
  (log_bytes:erased bytes)
  (len:U32.t)
  (log:larray U8.t len) //concrete log
  (outlen:U32.t)
  (out_bytes:erased bytes)
  (out:larray U8.t outlen) //out array, to write outputs
  (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
  (r_log_pos:R.ref (seq_index log_bytes))
  (r_out_pos:R.ref (seq_index out_bytes))
  (r_res:R.ref verify_result)
  ()
  : STT bool
      (exists_ (inv tsm t log_perm log_bytes len log outlen out_bytes out aeh r_log_pos r_out_pos r_res))
      (fun b -> inv tsm t log_perm log_bytes len log outlen out_bytes out aeh r_log_pos r_out_pos r_res b)
  = let _ = elim_exists () in
    let g_log_pos = elim_exists () in
    let g_res = elim_exists () in
    let g_out_pos = elim_exists () in
    elim_pure _;
    let res = R.read r_res in
    let log_pos = R.read r_log_pos in
    let b = Verify_success? res && U32.(log_pos <^ len) in
    intro_pure (inv_pure_pred len b g_res g_log_pos g_out_pos);
    intro_exists (reveal g_out_pos)
                 (fun out_pos ->
                  R.pts_to r_out_pos full_perm out_pos
                    `star`
                  inv_local_refs tsm t log_bytes len outlen out_bytes out aeh r_log_pos r_out_pos r_res b g_log_pos g_res out_pos);
    intro_exists (reveal g_res)
                 (fun res ->
                  R.pts_to r_res full_perm res
                    `star`
                  inv_out_pos tsm t log_bytes len outlen out_bytes out aeh r_log_pos r_out_pos r_res b g_log_pos res);
    intro_exists (reveal g_log_pos)
                 (fun log_pos ->
                  R.pts_to r_log_pos full_perm log_pos
                    `star`
                  inv_res tsm t log_bytes len outlen out_bytes out aeh r_log_pos r_out_pos r_res b log_pos);
    return b

// let verify_log_body (#tsm:M.thread_state_model)
//   (t:thread_state_t) //handle to the thread state
//   (#log_perm:perm)
//   (#log_bytes:erased bytes)
//   (#len:U32.t)
//   (log:larray U8.t len) //concrete log
//   (log_pos: _)
//   (#outlen:U32.t)
//   (#out_bytes:erased bytes)
//   (out_pos:U32.t{U32.v out_pos <= Seq.length out_bytes})
//   (out:larray U8.t outlen) //out array, to write outputs
//   (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
//   : ST verify_result
//     (//precondition
//       A.pts_to log log_perm log_bytes `star` //the log contains log_bytes
//       verify_post tsm t log_bytes out_bytes out aeh (Verify_success log_pos out_pos))
//     (fun res -> //postcondition
//       A.pts_to log log_perm log_bytes `star` //log contents didn't change
//       verify_post tsm t log_bytes out_bytes out aeh res)
//     (requires U32.v log_pos < U32.v len)
//     (ensures fun res -> True) //verify_result_complete len res)
//    =   A.pts_to_length log _;
//        let _log = elim_exists () in
//        let _out_bytes_1 = elim_exists () in
//        elim_pure _;
//        elim_pure _;
//        A.pts_to_length out _;
//        let is_failed = VerifierSteps.check_failed t in
//        if is_failed
//        then (
//          intro_some_failure t out aeh;
//          let res = Verify_entry_failure log_pos in
//          intro_pure (Parsing_failure? res ==>
//                      ~ (LogEntry.can_parse_log_entry log_bytes (Parsing_failure?.log_pos res)));
//          rewrite (some_failure t out aeh `star` pure _)
//                  (verify_post tsm t log_bytes out_bytes out aeh res);
//          return res
//        )
//        else (
//          assert (not (M.verify_model tsm _log).failed);
//          let res = verify_step t log_pos log out_pos out aeh in
//          assert_ (verify_step_post (M.verify_model tsm _log) t log_bytes log_pos _out_bytes_1 out_pos out aeh res);
//          match res
//                returns
//                  ST verify_result
//                  (//precondition
//                    A.pts_to log log_perm log_bytes `star`
//                    verify_step_post (M.verify_model tsm _log) t log_bytes log_pos _out_bytes_1 out_pos out aeh res)
//                  (fun res' -> //postcondition
//                    A.pts_to log log_perm log_bytes `star`
//                    verify_post tsm t log_bytes out_bytes out aeh res')
//                  (requires True)
//                  (ensures fun res -> True) //verify_result_complete len res)
//          with
//          | Parsing_failure loc ->
//            elim_verify_step_post_parsing_failure loc;
//            intro_some_failure t out aeh;
//            let res' = Parsing_failure loc in
//            intro_pure (Parsing_failure? res' ==>
//                        ~ (LogEntry.can_parse_log_entry log_bytes (Parsing_failure?.log_pos res')));
//            rewrite (some_failure t out aeh `star` pure _)
//                    (verify_post tsm t log_bytes out_bytes out aeh res');
//            return res'

//          | App_failure loc ->
//            elim_verify_step_post_app_failure loc;
//            let res' = App_failure loc in
//            intro_pure (Parsing_failure? res' ==>
//                        ~ (LogEntry.can_parse_log_entry log_bytes (Parsing_failure?.log_pos res')));
//            rewrite (some_failure t out aeh `star` pure _)
//                    (verify_post tsm t log_bytes out_bytes out aeh res');
//            return res'

//          | Verify_entry_failure loc ->
//            elim_verify_step_post_log_entry_failure loc;
//            let res' = res in
//            intro_pure (Parsing_failure? res' ==>
//                        ~ (LogEntry.can_parse_log_entry log_bytes (Parsing_failure?.log_pos res')));
//            rewrite (some_failure t out aeh `star` pure _)
//                    (verify_post tsm t log_bytes out_bytes out aeh res');
//            return res'

//          | Verify_success read wrote ->
//            let _ = stitch_verify_post_step #_ #tsm #t
//              #(Ghost.reveal log_bytes) log_pos out_bytes out_pos #_ #_ #_ #_ read wrote in
//            let res' = Verify_success U32.(log_pos +^ read) U32.(out_pos +^ wrote) in
//            return res'
//        )

#set-options "--print_implicits"

val verify_log_ind (#tsm:M.thread_state_model)
                   (t:thread_state_t) //handle to the thread state
                   (#log_perm:perm)
                   (#log_bytes:erased bytes)
                   (#len:U32.t)
                   (log:larray U8.t len) //concrete log
                   (log_pos:U32.t { U32.v log_pos <= Seq.length log_bytes })
                   (#outlen:U32.t)
                   (#out_bytes:erased bytes)
                   (out_pos:U32.t{U32.v out_pos <= Seq.length out_bytes})
                   (out:larray U8.t outlen) //out array, to write outputs
                   (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
  : ST verify_result
    (//precondition
      A.pts_to log log_perm log_bytes `star` //the log contains log_bytes
      verify_post tsm t log_bytes out_bytes out aeh (Verify_success log_pos out_pos))
    (fun res -> //postcondition
      A.pts_to log log_perm log_bytes `star` //log contents didn't change
      verify_post tsm t log_bytes out_bytes out aeh res)
    (requires True)
    (ensures fun res -> verify_result_complete len res)

let verify_log_ind
  (#tsm:M.thread_state_model)
  (t:thread_state_t) //handle to the thread state
  (#log_perm:perm)
  (#log_bytes:erased bytes)
  (#len:U32.t)
  (log:larray U8.t len) //concrete log
  (log_pos: _)
  (#outlen:U32.t)
  (#out_bytes:erased bytes)
  (out_pos:U32.t{U32.v out_pos <= Seq.length out_bytes})
  (out:larray U8.t outlen) //out array, to write outputs
  (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
  = A.pts_to_length log _;

    let r_log_pos = R.alloc #(seq_index log_bytes) 0ul in
    let r_out_pos = R.alloc #(seq_index out_bytes) 0ul in
    let r_res = R.alloc (Verify_success 0ul 0ul) in

    init_inv tsm t log_perm log_bytes len log outlen out_bytes out aeh r_log_pos r_out_pos r_res log_pos out_pos;

    Steel.ST.Loops.while_loop
      (inv tsm t log_perm log_bytes len log outlen out_bytes out aeh r_log_pos r_out_pos r_res)
      (verify_log_loop_cond tsm t log_perm log_bytes len log outlen out_bytes out aeh r_log_pos r_out_pos r_res)
      (verify_log_loop_body tsm t log_perm log_bytes len log outlen out_bytes out aeh r_log_pos r_out_pos r_res);

    let res = elim_inv_false tsm t log_perm log_bytes len log outlen out_bytes out aeh r_log_pos r_res r_out_pos in

    return res


#push-options "--fuel 1"

let intro_verify_post_success
               #o (#tsm:M.thread_state_model)
               (t:thread_state_t) //handle to the thread state
               (log_bytes:bytes { Seq.length log_bytes > 0 })
               (out_bytes:bytes)
               (out:A.array U8.t)
               (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate statew
   : STGhostT unit o
     (thread_state_inv t tsm `star`
      array_pts_to out out_bytes `star`
      TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false)
     (fun _ ->
       verify_post tsm t log_bytes out_bytes out aeh (Verify_success 0ul 0ul))
   = let les = Seq.empty in
     intro_pure (Log.parse_log_up_to log_bytes (U32.v 0ul) == Some les);
     intro_pure (Application.n_out_bytes tsm (M.verify_model tsm les) 0ul 0ul out_bytes out_bytes);
     intro_exists out_bytes (fun out_bytes1 ->
        array_pts_to out out_bytes1 `star`
        pure (Application.n_out_bytes tsm (M.verify_model tsm les) 0ul 0ul out_bytes out_bytes1));
     rewrite (thread_state_inv t tsm)
             (thread_state_inv t (M.verify_model tsm les));
     rewrite (TLM.tid_pts_to _ _ _ _ _)
             (TLM.tid_pts_to aeh.mlogs (M.verify_model tsm les).thread_id full
                                       (M.verify_model tsm les).processed_entries false);
     intro_exists les (fun log ->
       let tsm' = M.verify_model tsm log in
       pure (Log.parse_log_up_to log_bytes (U32.v 0ul) == Some log) `star`
       thread_state_inv t tsm' `star` //tsm' is the new state of the thread
       TLM.tid_pts_to aeh.mlogs tsm'.thread_id full tsm'.processed_entries false `star`
       exists_ (fun out_bytes1 ->
         array_pts_to out out_bytes1 `star`
         pure (Application.n_out_bytes tsm tsm' 0ul 0ul out_bytes out_bytes1)));
     rewrite_with (exists_ (fun log ->
       let tsm' = M.verify_model tsm log in
       pure (Log.parse_log_up_to log_bytes (U32.v 0ul) == Some log) `star`
       thread_state_inv t tsm' `star` //tsm' is the new state of the thread
       TLM.tid_pts_to aeh.mlogs tsm'.thread_id full tsm'.processed_entries false `star`
       exists_ (fun out_bytes1 ->
         array_pts_to out out_bytes1 `star`
         pure (Application.n_out_bytes tsm tsm' 0ul 0ul out_bytes out_bytes1))))
       (verify_post tsm t log_bytes out_bytes out aeh (Verify_success 0ul 0ul))
       (_ by (FStar.Tactics.trefl()))

let verify_log (#tsm:M.thread_state_model)
               (t:thread_state_t) //handle to the thread state
               (#log_perm:perm)
               (#log_bytes:erased bytes)
               (#len:U32.t { len <> 0ul })
               (log:larray U8.t len) //concrete log
               (#outlen:U32.t)
               (#out_bytes:erased bytes)
               (out:larray U8.t outlen) //out array, to write outputs
               (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate statew
  : STT (v:verify_result { verify_result_complete len v })
    (//precondition
      A.pts_to log log_perm log_bytes `star` //the log contains log_bytes
      thread_state_inv t tsm `star`
      array_pts_to out out_bytes `star`
      TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false)
    (fun res -> //postcondition
      A.pts_to log log_perm log_bytes `star` //log contents didn't change
      verify_post tsm t log_bytes out_bytes out aeh res)
   = A.pts_to_length log _;
     intro_verify_post_success t log_bytes out_bytes out aeh;
     verify_log_ind t log 0ul 0ul out aeh
