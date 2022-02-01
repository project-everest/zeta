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
let spec_parser_log  = admit()
let bytes_from (b:bytes)
               (l:U32.t { U32.v l <= Seq.length b })
  : bytes
  = Seq.slice b (U32.v l) (Seq.length b)

val verify_step (#tsm:M.thread_state_model)
                (t:thread_state_t) //handle to the thread state
                (#log_perm:perm)
                (#log_bytes:erased bytes)
                (#len:U32.t)
                (log_pos:U32.t{U32.v log_pos < Seq.length log_bytes})
                (log:larray U8.t len) //concrete log
                (#outlen:U32.t)
                (out:larray U8.t outlen) //out array, to write outputs
                (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
  : STT (option (U32.t & U32.t))
    (//precondition
      A.pts_to log log_perm log_bytes `star` //the log contains log_bytes
      thread_state_inv t tsm `star` //thread state is initially tsm
      exists_ (array_pts_to out) `star` //we have permission to out, don't care what it contains
      TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false //and the global state contains this thread's entries
    )
    (fun res -> //postcondition
      A.pts_to log log_perm log_bytes `star` //log contents didn't change
      (match res with
       | None ->
         //if it fails, you still get back ownership on the various
         //resources, e.g., to free them
         //but not much else
         exists_ (thread_state_inv t) `star`
         exists_ (array_pts_to out)
      | Some (n_read, n_out) ->
         //it succeeded
         exists_ (fun (tsm':M.thread_state_model) ->
         exists_ (fun (out_bytes:Seq.seq U8.t) ->
           thread_state_inv t tsm' `star` //tsm' is the new state of the thread
           array_pts_to out out_bytes `star`  //the out array contains out_bytes
           TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm'.processed_entries false `star` //my contributions are updated
           pure (
             match LogEntry.spec_parser_log_entry (bytes_from log_bytes log_pos) with
             | None -> False //log parsing did not fail
             | Some (log_entry, n_read') -> //parsing produces log_entries
               U32.v n_read == n_read' /\
               //tsm' what you get by running the spec verifier from tsm on log_entries
               tsm' == M.verify_step_model tsm log_entry /\
               //the out_bytes contain any new app results in tsm'
               out_bytes == M.bytes_of_app_results (M.delta_app_results tsm tsm') /\
               //and n_out is the number of bytes that were written
               U32.v n_out == Seq.length out_bytes
           )
           ))))
let verify_step (#tsm:M.thread_state_model)
                (t:thread_state_t) //handle to the thread state
                (#log_perm:perm)
                (#log_bytes:erased bytes)
                (#len:U32.t)
                (log_pos:U32.t{U32.v log_pos < Seq.length log_bytes})
                (log:larray U8.t len) //concrete log
                (#outlen:U32.t)
                (out:larray U8.t outlen) //out array, to write outputs
                (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
    = admit__()
