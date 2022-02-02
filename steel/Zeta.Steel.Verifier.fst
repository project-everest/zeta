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
let spec_parser_log  = admit()

let compat_with_any_anchor_of_le (l:TLM.log)
                                 (le:log_entry { not (VerifyEpoch? le) })
  : Lemma (l `TLM.log_grows` (Seq.snoc l le) /\
           (Seq.snoc l le) `TLM.compat_with_any_anchor_of` l)
          [SMTPat (Seq.snoc l le)]
  = admit()

let fail (#p:prop)
         (#tsm:M.thread_state_model)
         (#entries:erased _)
         (#tid:erased _)
         (t:thread_state_t)
         (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
         (#outlen:U32.t)
         (#out_bytes:erased _)
         (out:larray U8.t outlen) //out array, to write outputs
  : STT unit
    (thread_state_inv t tsm `star`
     TLM.tid_pts_to aeh.mlogs tid full entries false `star`
     array_pts_to out out_bytes `star`
     pure p)
    (fun _ ->
      exists_ (thread_state_inv t) `star`
      exists_ (array_pts_to out) `star`
      exists_ (fun entries -> TLM.tid_pts_to aeh.mlogs tid full entries false))
  = intro_exists _ (thread_state_inv t);
    intro_exists _ (fun entries -> TLM.tid_pts_to aeh.mlogs tid full entries false);
    intro_exists _ (array_pts_to out);
    elim_pure _;
    ()

let intro_nout_bytes //(#o:_)
                     (tsm tsm':M.thread_state_model)
                     (out_bytes:erased bytes)
  : ST unit
    emp
    (fun _ -> pure (Application.n_out_bytes tsm tsm' 0ul out_bytes out_bytes))
    (requires Application.delta_out_bytes tsm tsm' == Seq.empty)
    (ensures fun _ -> True)
  = admit__()

let verify_log_entry_post (tsm:M.thread_state_model)
                          (t:thread_state_t)
                          (#outlen:U32.t)
                          (out_bytes0:bytes)
                          (out:larray U8.t outlen) //out array, to write outputs
                          (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
                          (le:LogEntry.log_entry)
                          ([@@@smt_fallback] res:option U32.t)
  : vprop
  = match res with
    | None ->
         //if it fails, you still get back ownership on the various
         //resources, e.g., to free them
         //but not much else
         exists_ (thread_state_inv t) `star`
         exists_ (array_pts_to out) `star`
         exists_ (fun entries -> TLM.tid_pts_to aeh.mlogs tsm.thread_id full entries false)

    | Some n_out ->
         //it succeeded
         let tsm' = M.verify_step_model tsm le in
         exists_ (fun (out_bytes1:Seq.seq U8.t) ->
           thread_state_inv t tsm' `star` //tsm' is the new state of the thread
           array_pts_to out out_bytes1 `star`  //the out array contains out_bytes
           TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm'.processed_entries false `star` //my contributions are updated
           pure (Application.n_out_bytes tsm tsm' n_out out_bytes0 out_bytes1))

let success (#o:_)
            (#tsm:M.thread_state_model)
            (t:thread_state_t)
            (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
            (#outlen:U32.t)
            (#out_bytes0 #out_bytes1:erased _)
            (out:larray U8.t outlen) //out array, to write outputs
            (le:log_entry)
            (n_out:U32.t)
  : STGhostT unit o
    (thread_state_inv t (M.verify_step_model tsm le) `star`
     TLM.tid_pts_to aeh.mlogs tsm.thread_id full (M.verify_step_model tsm le).processed_entries false `star`
     array_pts_to out out_bytes1 `star`
     pure (Application.n_out_bytes tsm (M.verify_step_model tsm le) n_out out_bytes0 out_bytes1))
    (fun _ ->
      verify_log_entry_post tsm t out_bytes0 out aeh le (Some n_out))
       // let tsm' = M.verify_step_model tsm le in
       // exists_ (fun (out_bytes1:Seq.seq U8.t) ->
       //   thread_state_inv t tsm' `star` //tsm' is the new state of the thread
       //   array_pts_to out out_bytes1 `star`  //the out array contains out_bytes
       //   TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm'.processed_entries false `star` //my contributions are updated
       //   pure (Application.n_out_bytes tsm tsm' n_out out_bytes0 out_bytes1)))
  = let tsm' = M.verify_step_model tsm le in
    intro_exists_erased out_bytes1
       (fun (out_bytes1:Seq.seq U8.t) ->
         thread_state_inv t tsm' `star` //tsm' is the new state of the thread
         array_pts_to out out_bytes1 `star`  //the out array contains out_bytes
         TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm'.processed_entries false `star` //my contributions are updated
         pure (Application.n_out_bytes tsm tsm' n_out out_bytes0 out_bytes1))



val verify_entry_cases (#tsm:M.thread_state_model)
                       (t:thread_state_t) //handle to the thread state
                       (#outlen:U32.t)
                       (#out_bytes0:erased bytes)
                       (out:larray U8.t outlen) //out array, to write outputs
                       (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
                       (le:LogEntry.log_entry)
                       (b:bool)
  : ST (option U32.t)
    (thread_state_inv t (update_if b tsm (M.verify_step_model tsm le)) `star`
     TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false `star`
     array_pts_to out out_bytes0)
    (fun res -> verify_log_entry_post tsm t out_bytes0 out aeh le res)
    (requires
      not (VerifyEpoch? le) /\ not (RunApp? le) /\
      not tsm.failed)
    (ensures fun _ -> True)
//fusing val and let leads to errors
let verify_entry_cases (#tsm:M.thread_state_model)
                       (t:thread_state_t) //handle to the thread state
                       (#outlen:U32.t)
                       (#out_bytes0:erased bytes)
                       (out:larray U8.t outlen) //out array, to write outputs
                       (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
                       (le:LogEntry.log_entry)
                       (b:bool)
  = snoc_entries tsm le;
    compat_with_any_anchor_of_le tsm.processed_entries le;
    TLM.update_tid_log aeh.mlogs tsm.thread_id tsm.processed_entries (M.verify_step_model tsm le).processed_entries;
    intro_nout_bytes tsm (M.verify_step_model tsm le) out_bytes0;
    if b
    then (
      rewrite (thread_state_inv t _)
              (thread_state_inv t (M.verify_step_model tsm le));
      success t aeh out le 0ul;
      return (Some 0ul)
    )
    else (
      rewrite (thread_state_inv t _)
              (thread_state_inv t tsm);
      fail t aeh out;
      return None
    )

val verify_log_entry (#tsm:M.thread_state_model)
                     (t:thread_state_t) //handle to the thread state
                     (#outlen:U32.t)
                     (#outbytes0:erased bytes)
                     (out:larray U8.t outlen) //out array, to write outputs
                     (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
                     (le:LogEntry.log_entry)
  : ST (option U32.t)
    (//precondition
      thread_state_inv t tsm `star` //thread state is initially tsm
      array_pts_to out outbytes0 `star` //we have permission to out, don't care what it contains
      TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false //and the global state contains this thread's entries
    )
    (fun res -> //postcondition
      verify_log_entry_post tsm t outbytes0 out aeh le res)
    (requires not tsm.failed /\
              not (RunApp? le))
    (ensures fun _ -> True)

#push-options "--query_stats --fuel 0 --ifuel 1 --z3rlimit_factor 3"

let verify_log_entry (#tsm:M.thread_state_model)
                     (t:thread_state_t) //handle to the thread state
                     (#outlen:U32.t)
                     (#out_bytes:erased bytes)
                     (out:larray U8.t outlen) //out array, to write outputs
                     (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
                     (le:LogEntry.log_entry)
   = snoc_entries tsm le;
     match le with
     | VerifyEpoch ->
       let b = VerifierSteps.verify_epoch t aeh in
       intro_nout_bytes tsm (M.verify_step_model tsm le) out_bytes;
       if b
       then (
         rewrite (thread_state_inv t _)
                 (thread_state_inv t (M.verify_step_model tsm le));
         success t aeh out le 0ul;
         return (Some 0ul)
       )
       else (
         rewrite (thread_state_inv t _)
                 (thread_state_inv t tsm);
         fail t aeh out;
         return None
       )

     | _ ->
       // compat_with_any_anchor_of_le tsm.processed_entries le;
       // TLM.update_tid_log aeh.mlogs tsm.thread_id tsm.processed_entries (M.verify_step_model tsm le).processed_entries;
       // intro_nout_bytes tsm (M.verify_step_model tsm le) out_bytes;
       match le with
       | AddM s s' r ->
         let b = VerifierSteps.vaddm t s s' r in
         verify_entry_cases t out aeh le b

       | AddB s ts tid r ->
         let b = VerifierSteps.vaddb t s ts tid r in
         verify_entry_cases t out aeh le b

       | EvictM pl ->
         VerifierSteps.vevictm t pl.s pl.s';
         verify_entry_cases t out aeh le true

       | EvictB pl ->
         let b = VerifierSteps.vevictb t pl.s pl.t in
         verify_entry_cases t out aeh le b

       | EvictBM pl ->
         let b = VerifierSteps.vevictbm t pl.s pl.s' pl.t in
         verify_entry_cases t out aeh le b

       | NextEpoch ->
         let b = VerifierSteps.nextepoch t in
         verify_entry_cases t out aeh le true

type verify_step_result =
  | Parsing_failure: verify_step_result
  | App_failure: verify_step_result
  | Verify_log_entry_failure: verify_step_result
  | Verify_log_entry_success: read:U32.t -> wrote:U32.t -> verify_step_result

let verify_step_post (tsm:M.thread_state_model)
                     (t:thread_state_t) //handle to the thread state
                     (log_perm:perm)
                     (log_bytes:bytes)
                     (#len:U32.t)
                     (log_pos:U32.t{U32.v log_pos < Seq.length log_bytes})
                     (log:larray U8.t len) //concrete log
                     (#outlen:U32.t)
                     (out_bytes:bytes)
                     (out:larray U8.t outlen) //out array, to write outputs
                     (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
                     ([@@@smt_fallback] res:verify_step_result)
 : vprop
 = match res with
   | Parsing_failure ->
      pure (LogEntry.spec_parser_log_entry (Parser.bytes_from log_bytes log_pos) == None) `star`
      thread_state_inv t tsm `star`
      TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false `star`
      array_pts_to out out_bytes

   | App_failure ->
      thread_state_inv t tsm `star`
      TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false `star`
      array_pts_to out out_bytes

   | Verify_log_entry_failure ->
      (match (LogEntry.spec_parser_log_entry (Parser.bytes_from log_bytes log_pos)) with
       | None -> pure False
       | Some (le, _) -> verify_log_entry_post tsm t out_bytes out aeh le None)

   | Verify_log_entry_success read wrote ->
      (match (LogEntry.spec_parser_log_entry (Parser.bytes_from log_bytes log_pos)) with
       | None -> pure False
       | Some _ ->
         pure (snd (LogEntry.spec_parse_log_entry log_bytes log_pos) == U32.v read) `star`
         verify_log_entry_post tsm t out_bytes out aeh
           (fst (LogEntry.spec_parse_log_entry log_bytes log_pos))
           (Some wrote))

let intro_verify_step_post_parsing_failure
                     (#o:_)
                     (#tsm:M.thread_state_model)
                     (t:thread_state_t) //handle to the thread state
                     (#log_perm:perm)
                     (#log_bytes:erased bytes)
                     (#len:U32.t)
                     (log_pos:U32.t{U32.v log_pos < Seq.length log_bytes})
                     (log:larray U8.t len) //concrete log
                     (#outlen:U32.t)
                     (out_bytes:bytes)
                     (out:larray U8.t outlen) //out array, to write outputs
                     (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
  : STGhost unit o
    (thread_state_inv t tsm `star`
     TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false `star`
     array_pts_to out out_bytes)
    (fun _ ->
      verify_step_post tsm t log_perm log_bytes log_pos log out_bytes out aeh Parsing_failure)
    (requires
      LogEntry.spec_parser_log_entry (Parser.bytes_from log_bytes log_pos) == None)
    (ensures fun _ -> True)
  = intro_pure (LogEntry.spec_parser_log_entry (Parser.bytes_from log_bytes log_pos) == None);
    rewrite (pure _ `star`
             thread_state_inv t tsm `star`
             TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false `star`
             array_pts_to out out_bytes)
             _

let intro_verify_step_post_app_failure
                     (#o:_)
                     (#tsm:M.thread_state_model)
                     (t:thread_state_t) //handle to the thread state
                     (#log_perm:perm)
                     (#log_bytes:erased bytes)
                     (#len:U32.t)
                     (log_pos:U32.t{U32.v log_pos < Seq.length log_bytes})
                     (log:larray U8.t len) //concrete log
                     (#outlen:U32.t)
                     (out_bytes:bytes)
                     (out:larray U8.t outlen) //out array, to write outputs
                     (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
  : STGhostT unit o
    (thread_state_inv t tsm `star`
     TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false `star`
     array_pts_to out out_bytes)
    (fun _ ->
      verify_step_post tsm t log_perm log_bytes log_pos log out_bytes out aeh App_failure)
  = rewrite (thread_state_inv t tsm `star`
             TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false `star`
             array_pts_to out out_bytes)
             _

let intro_verify_step_post_verify_failure
                     (#o:_)
                     (#tsm:M.thread_state_model)
                     (t:thread_state_t) //handle to the thread state
                     (#log_perm:perm)
                     (#log_bytes:erased bytes)
                     (#len:U32.t)
                     (log_pos:U32.t{U32.v log_pos < Seq.length log_bytes})
                     (log:larray U8.t len) //concrete log
                     (#outlen:U32.t)
                     (out_bytes:bytes)
                     (out:larray U8.t outlen) //out array, to write outputs
                     (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
                     (le: log_entry)
  : STGhost unit o
    (verify_log_entry_post tsm t out_bytes out aeh le None)
    (fun _ ->
      verify_step_post tsm t log_perm log_bytes log_pos log out_bytes out aeh Verify_log_entry_failure)
    (requires
       (match (LogEntry.spec_parser_log_entry (Parser.bytes_from log_bytes log_pos)) with
       | None -> False
       | Some (le', n') -> le == le'))
    (ensures fun _ -> True)
  = rewrite _ _

let intro_verify_step_post_verify_success
                     (#o:_)
                     (#tsm:M.thread_state_model)
                     (t:thread_state_t) //handle to the thread state
                     (#log_perm:perm)
                     (#log_bytes:erased bytes)
                     (#len:U32.t)
                     (log_pos:U32.t{U32.v log_pos < Seq.length log_bytes})
                     (log:larray U8.t len) //concrete log
                     (#outlen:U32.t)
                     (out_bytes:bytes)
                     (out:larray U8.t outlen) //out array, to write outputs
                     (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
                     (le: log_entry)
                     (n_read:U32.t)
                     (n_written:U32.t)
  : STGhost unit o
    (verify_log_entry_post tsm t out_bytes out aeh le (Some n_written))
    (fun _ ->
      verify_step_post tsm t log_perm log_bytes log_pos log out_bytes out aeh (Verify_log_entry_success n_read n_written))
    (requires
       LogEntry.can_parse_log_entry log_bytes log_pos /\
       LogEntry.spec_parse_log_entry log_bytes log_pos == (le, U32.v n_read))
    (ensures fun _ -> True)
  = intro_pure (snd (LogEntry.spec_parse_log_entry log_bytes log_pos) == U32.v n_read);
    rewrite (pure _ `star`
             verify_log_entry_post tsm t out_bytes out aeh le (Some n_written))
             _

let intro_verify_step_post_runapp_success
                     (#o:_)
                     (#tsm:M.thread_state_model)
                     (t:thread_state_t) //handle to the thread state
                     (#log_perm:perm)
                     (#log_bytes:erased bytes)
                     (#len:U32.t)
                     (log_pos:U32.t{U32.v log_pos < Seq.length log_bytes})
                     (log:larray U8.t len) //concrete log
                     (#outlen:U32.t)
                     (out_bytes:bytes)
                     (out:larray U8.t outlen) //out array, to write outputs
                     (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
                     (le: log_entry)
                     (n_read:U32.t)
                     (n_written:U32.t)
                     (res:Application.verify_runapp_result)
  : STGhost unit o
    (Application.verify_runapp_entry_post tsm t #len log_pos log_bytes out_bytes out res `star`
     TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false)
    (fun _ ->
      verify_step_post tsm t log_perm log_bytes log_pos log out_bytes out aeh (Verify_log_entry_success n_read n_written))
    (requires res == Application.Run_app_success n_read n_written /\ not tsm.failed)
    (ensures fun _ -> True)
  = rewrite (Application.verify_runapp_entry_post tsm t #len log_pos log_bytes out_bytes out res)
            (Application.verify_runapp_entry_post tsm t #len log_pos log_bytes out_bytes out (Application.Run_app_success n_read n_written));
    let pl = elim_exists () in
    let out_bytes' = elim_exists () in
    elim_pure _;
    assert_ (thread_state_inv t (M.verify_step_model tsm (RunApp pl)));
    assert_ (array_pts_to out out_bytes');
    snoc_entries tsm (RunApp pl);
    compat_with_any_anchor_of_le tsm.processed_entries (RunApp pl);
    TLM.update_tid_log aeh.mlogs tsm.thread_id tsm.processed_entries (M.verify_step_model tsm (RunApp pl)).processed_entries;
    intro_pure (Application.n_out_bytes tsm (M.verify_step_model tsm (RunApp pl)) n_written  out_bytes out_bytes');
    success t aeh out (RunApp pl) n_written;
    intro_verify_step_post_verify_success #_ #tsm t #log_perm #log_bytes #len log_pos log #outlen out_bytes out aeh (RunApp pl) n_read n_written

val verify_step (#tsm:M.thread_state_model)
                (t:thread_state_t) //handle to the thread state
                (#log_perm:perm)
                (#log_bytes:erased bytes)
                (#len:U32.t)
                (log_pos:U32.t{U32.v log_pos < Seq.length log_bytes})
                (log:larray U8.t len) //concrete log
                (#outlen:U32.t)
                (#out_bytes:erased bytes)
                (out_pos:U32.t{U32.v out_pos < Seq.length out_bytes})
                (out:larray U8.t outlen) //out array, to write outputs
                (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
  : ST verify_step_result
    (//precondition
      A.pts_to log log_perm log_bytes `star` //the log contains log_bytes
      thread_state_inv t tsm `star` //thread state is initially tsm
      array_pts_to out out_bytes `star` //we have permission to out, don't care what it contains
      TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false //and the global state contains this thread's entries
    )
    (fun res -> //postcondition
      A.pts_to log log_perm log_bytes `star` //log contents didn't change
      verify_step_post tsm t log_perm log_bytes log_pos log out_bytes out aeh res)
    (requires not tsm.failed)
    (ensures fun _ -> True)

let verify_step (#tsm:M.thread_state_model)
                (t:thread_state_t) //handle to the thread state
                (#log_perm:perm)
                (#log_bytes:erased bytes)
                (#len:U32.t)
                (log_pos:U32.t{U32.v log_pos < Seq.length log_bytes})
                (log:larray U8.t len) //concrete log
                (#out_len:U32.t)
                (#out_bytes:erased bytes)
                (out_pos:U32.t{U32.v out_pos < Seq.length out_bytes})
                (out:larray U8.t out_len) //out array, to write outputs
                (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
    = A.pts_to_length log _;
      let res = LogEntry.parser_log_entry len log_pos U32.(len -^ log_pos) log in
      match res with
      | None ->
        intro_verify_step_post_parsing_failure t log_pos log out_bytes out aeh;
        return Parsing_failure

      | Some (le, read) ->
        match le with
        | RunApp _ ->
          let app_res =
            Application.run_app_function
              len log_pos log
              out_len 0ul out
              t
          in
          begin
          match app_res with
          | Application.Run_app_parsing_failure
          | Application.Run_app_verify_failure ->
            rewrite (Application.verify_runapp_entry_post _ _ _ _ _ _ _)
                    (thread_state_inv t tsm `star`
                     array_pts_to out out_bytes);
            intro_verify_step_post_app_failure t log_pos log out_bytes out aeh;
            return App_failure

          | Application.Run_app_success read written ->
//            assert_ (Application.verify_runapp_entry_post tsm t log_pos log_bytes out_bytes out app_res);
            let _ = intro_verify_step_post_runapp_success #_ #tsm t #log_perm #log_bytes log_pos log out_bytes out aeh le read written app_res in
            return (Verify_log_entry_success read written)
          end

        | _ ->
          let b = verify_log_entry t out aeh le in
          match b with
          | None ->
            rewrite (verify_log_entry_post tsm t out_bytes out aeh le b)
                    (verify_step_post tsm t log_perm log_bytes log_pos log out_bytes out aeh Verify_log_entry_failure);
            return Verify_log_entry_failure

          | Some written ->
            rewrite (verify_log_entry_post tsm t out_bytes out aeh le b)
                    (verify_log_entry_post tsm t out_bytes out aeh le (Some written));
            intro_verify_step_post_verify_success t #log_perm log_pos log out_bytes out aeh le read written;
            return (Verify_log_entry_success read written)
