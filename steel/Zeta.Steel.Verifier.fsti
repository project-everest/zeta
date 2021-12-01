module Zeta.Steel.Verifier
include Zeta.Steel.VerifierTypes
open FStar.Ghost
open Steel.ST.Util
module G = Steel.ST.GhostReference
module R = Steel.ST.Reference
module A = Steel.ST.Array
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

#push-options "--ide_id_info_off"

val spec_parser_log : P.spec_parser (Seq.seq log_entry_base)

let parse_log (l:bytes) =
  match spec_parser_log l with
  | None -> None
  | Some (v, n) ->
    if n = Seq.length l
    then Some v
    else None

val create (tid:T.thread_id)
  : STT thread_state_t
    emp
    (fun t -> thread_state_inv t (M.init_thread_state_model tid))

let delta_app_results (tsm0 tsm1:M.thread_state_model)
  : GTot (Seq.seq M.app_results)
  = Prims.admit()

let bytes_of_app_results (s:Seq.seq M.app_results)
  : GTot bytes
  = Prims.admit()

/// Entry point to run a single verifier thread on a log
val verify (#tsm:M.thread_state_model)
           (t:thread_state_t) //handle to the thread state
           (#log_bytes:erased bytes)
           (#len:U32.t)
           (log:larray U8.t len) //concrete log
           (#outlen:U32.t)
           (out:larray U8.t outlen) //out array, to write outputs
           (#logrefs: erased (AEH.log_refs_t))
           (aeh:AEH.aggregate_epoch_hashes logrefs) //lock & handle to the aggregate state
           (mylogref:AEH.log_ref { //this thread's contribution to the aggregate state
             Map.sel logrefs tsm.thread_id == mylogref
            })
  : STT (option U32.t)
    (//precondition
      thread_state_inv t tsm `star` //thread state is initially tsm
      A.pts_to log log_bytes `star` //the log contains log_bytes
      exists_ (A.pts_to out) `star` //we have permission to out, don't care what it contains
      G.pts_to mylogref half (M.committed_entries tsm) //and mylogref contains this thread's committed entries
    )
    (fun res -> //postcondition
      A.pts_to log log_bytes `star` //log contents didn't change
      (match res with
       | None ->
         //if it fails, you still get back ownership on the various
         //resources, e.g., to free them
         //but not much else
         exists_ (thread_state_inv t) `star`
         exists_ (A.pts_to out) `star`
         exists_ (G.pts_to mylogref half)
      | Some n_out ->
         //it succeeded
         exists_ (fun (tsm':M.thread_state_model) ->
         exists_ (fun (out_bytes:Seq.seq U8.t) ->
           thread_state_inv t tsm' `star` //tsm' is the new state of the thread
           A.pts_to out out_bytes `star`  //the out array contains out_bytes
           G.pts_to mylogref half (M.committed_entries tsm') `star` //my contributions are updated
           pure (
             match parse_log log_bytes with
             | None -> False //log parsing did not fail
             | Some log_entries -> //parsing produces log_entries
               //tsm' what you get by running the spec verifier from tsm on log_entries
               tsm' == M.verify_model tsm log_entries /\
               //the out_bytes contain any new app results in tsm'
               out_bytes == bytes_of_app_results (delta_app_results tsm tsm') /\
               //and n_out is the number of bytes that were written
               U32.v n_out == Seq.length out_bytes
           )
           ))))
