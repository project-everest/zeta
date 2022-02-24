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
#push-options "--ide_id_info_off"

[@@CAbstractStruct]
val top_level_state : Type0

val core_inv (t:top_level_state) : vprop

let tid_log_map = 
  x:Map.t tid (option M.log) { 
    Map.domain x `Set.equal` Set.complement Set.empty 
  }

val all_logs   (t:top_level_state) (_ : tid_log_map) : vprop

val log_of_tid (t:top_level_state) (tid:tid) (l:M.log) : vprop

val snapshot (t:top_level_state) (_ : tid_log_map) : vprop

// This creates a Zeta instance
val init (_:unit)
  : STT top_level_state
        emp
        (fun t -> core_inv t `star`
               all_logs t (Map.const (Some Seq.empty)))

let verify_post_success_pure_inv
  (tid:tid)
  (entries:erased AEH.log)
  (log_bytes:erased bytes)
  (out_bytes:erased bytes)
  (read wrote:U32.t)  
  (entries':Seq.seq log_entry)
  (out_bytes':Seq.seq U8.t)
  : prop
  = Log.parse_log_up_to log_bytes (U32.v read) == Some entries' /\
    (let tsm = M.verify_model (M.init_thread_state_model tid) entries in
     let tsm' = M.verify_model tsm entries' in
     Application.n_out_bytes tsm tsm' 0ul wrote out_bytes out_bytes')

[@@ __reduce__]
let verify_post_success_out_bytes_pred
  (t:top_level_state)
  (tid:tid)
  (entries:erased AEH.log)
  (log_bytes:erased bytes)
  (out_len: U32.t)
  (out_bytes:erased bytes)
  (output:larray U8.t out_len)
  (read wrote:U32.t)
  (entries':Seq.seq log_entry)
  : Seq.seq U8.t -> vprop
  = fun out_bytes' ->
    log_of_tid t tid (entries `Seq.append` entries')
      `star`
    A.pts_to output full_perm out_bytes'
      `star`
    pure (verify_post_success_pure_inv
            tid
            entries
            log_bytes
            out_bytes
            read
            wrote
            entries'
            out_bytes')

[@@ __reduce__]
let verify_post_success_pred
  (t:top_level_state)
  (tid:tid)
  (entries:erased AEH.log)
  (log_bytes:erased bytes)
  (out_len: U32.t)
  (out_bytes:erased bytes)
  (output:larray U8.t out_len)
  (read wrote:U32.t)
  : Seq.seq log_entry -> vprop
  = fun entries' ->
    exists_ (verify_post_success_out_bytes_pred
               t
               tid
               entries
               log_bytes
               out_len
               out_bytes
               output
               read
               wrote
               entries')

let verify_post
  (t:top_level_state)
  (tid:tid)
  (entries:erased AEH.log)
  (log_perm:perm)
  (log_bytes:erased bytes)
  (len: U32.t)
  (input:larray U8.t len)
  (out_len: U32.t)
  (out_bytes:erased bytes)
  (output:larray U8.t out_len)
  : post_t (option (v:V.verify_result { V.verify_result_complete len v }))
  = fun res ->
    core_inv t `star`
    A.pts_to input log_perm log_bytes `star`
    (match res with
     | Some (V.Verify_success read wrote) ->
       exists_ (verify_post_success_pred
                  t
                  tid
                  entries
                  log_bytes
                  out_len
                  out_bytes
                  output
                  read
                  wrote)

     | _ ->
       exists_ (fun s -> A.pts_to output full_perm s) `star`
       exists_ (fun entries' -> log_of_tid t tid entries'))

val verify_log (t:top_level_state)
               (tid:tid)
               (#entries:erased AEH.log)
               (#log_perm:perm)
               (#log_bytes:erased bytes)
               (len: U32.t { len <> 0ul })
               (input:larray U8.t len)
               (out_len: U32.t)
               (#out_bytes:erased bytes)
               (output:larray U8.t out_len)
  : STT (option (v:V.verify_result { V.verify_result_complete len v }))
    (core_inv t `star`
     A.pts_to input log_perm log_bytes `star`
     A.pts_to output full_perm out_bytes `star`
     log_of_tid t tid entries)
    (verify_post t tid entries log_perm log_bytes len input out_len out_bytes output)


[@@ __reduce__]
let read_max_post_pred (t:top_level_state) (max:M.epoch_id)
  : AEH.all_processed_entries -> vprop
  = fun logs ->
    snapshot t (AEH.map_of_seq logs)
      `star`
    pure (AEH.max_is_correct logs max)

val max_certified_epoch (t:top_level_state)
  : STT AEH.max_certified_epoch_result
        emp 
        (fun r -> 
           match r with
           | AEH.Read_max_error  //underspec: overflow or element went missing in IArray
           | AEH.Read_max_none -> emp  //no epoch has been certified yet
           | AEH.Read_max_some max ->
             exists_ (fun logs ->
               snapshot t (AEH.map_of_seq logs)
               `star`
               pure (AEH.max_is_correct logs max)
               ))

//From this, we should connect back to the semantic
//proof and show that the entries are sequentially consistent up to eid
//except for hash collisions
