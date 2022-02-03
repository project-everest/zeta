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
module TLM = Zeta.Steel.ThreadLogMap

#push-options "--ide_id_info_off"
val parse_log_up_to (l:bytes) (pos:nat) : GTot (option M.log)

type verify_result =
  | Parsing_failure: log_pos:U32.t -> verify_result
  | App_failure: log_pos:U32.t -> verify_result
  | Verify_entry_failure: log_pos:U32.t -> verify_result
  | Verify_success: read:U32.t -> wrote:U32.t -> verify_result

let verify_result_complete (len:U32.t) res =
    match res with
    | Verify_success read _ ->
      read == len
    | _ -> True

[@@__steel_reduce__;__reduce__]
let some_failure (t:thread_state_t) //handle to the thread state
                 (out:A.array U8.t)
                 (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
  : vprop
  = exists_ (thread_state_inv t) `star`
    exists_ (fun entries -> TLM.tid_pts_to aeh.mlogs (VerifierTypes.thread_id t) full entries false) `star`
    exists_ (array_pts_to out)

let verify_post_out_bytes (tsm:M.thread_state_model)
                          (out_bytes:bytes)
                          (wrote:U32.t)
                          (out:A.array U8.t)
                          (les:M.log)
  : vprop
  = exists_ (fun (out_bytes1:Seq.seq U8.t) ->
     array_pts_to out out_bytes1 `star`  //the out array contains out_bytes
     pure (Application.n_out_bytes tsm (M.verify_model tsm les) 0ul wrote out_bytes out_bytes1))


let verify_post (tsm:M.thread_state_model)
                (t:thread_state_t) //handle to the thread state
                (log_bytes:bytes)
                (out_bytes:bytes)
                (out:A.array U8.t)
                (aeh:AEH.aggregate_epoch_hashes) //lock & handle to the aggregate state
                ([@@@smt_fallback] res:verify_result)
 : vprop
 = match res with
   | Parsing_failure log_pos ->
      pure (~ (LogEntry.can_parse_log_entry log_bytes log_pos) ) `star`
      some_failure t out aeh

   | App_failure _ ->
      some_failure t out aeh

   | Verify_entry_failure _ ->
      some_failure t out aeh

   | Verify_success read wrote ->
     exists_ (fun log ->
       let tsm' = M.verify_model tsm log in
       pure (parse_log_up_to log_bytes (U32.v read) == Some log) `star`
       thread_state_inv t tsm' `star` //tsm' is the new state of the thread
       TLM.tid_pts_to aeh.mlogs tsm'.thread_id full tsm'.processed_entries false `star` //my contributions are updated
       verify_post_out_bytes tsm out_bytes wrote out log)

val verify_log (#tsm:M.thread_state_model)
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
