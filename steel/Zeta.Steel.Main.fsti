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


let thread_inv_predicate
  (t:V.thread_state_t)
  (mlogs:TLM.t)
  : M.thread_state_model -> vprop
  = fun tsm ->
    V.thread_state_inv t tsm `star`
    TLM.tid_pts_to mlogs tsm.M.thread_id half tsm.M.processed_entries false

let thread_inv (t: V.thread_state_t)
               (mlogs: TLM.t)
  : vprop
  = exists_ (thread_inv_predicate t mlogs)

noeq
type thread_state (mlogs:TLM.t) =
{
  tid: tid;
  tsm: tsm:V.thread_state_t{V.thread_id tsm == tid};
  lock : cancellable_lock (thread_inv tsm mlogs)
}

let all_threads_t (mlogs:TLM.t) =
  larray (thread_state mlogs) n_threads

noeq
type top_level_state = {
  aeh: AEH.aggregate_epoch_hashes;
  all_threads : all_threads_t aeh.mlogs
}


let tid_positions_ok #l (all_threads: Seq.seq (thread_state l))
  : prop
  = forall (i:SA.seq_index all_threads).
        let si = Seq.index all_threads i in
        U16.v si.tid == i

let core_inv (t:top_level_state)
  : vprop
  = exists_ (fun perm ->
    exists_ (fun v ->
      A.pts_to t.all_threads perm v `star`
      pure (tid_positions_ok v)))

let tid_index = i:U16.t { U16.v i <= U32.v n_threads }

let rec forall_threads_between (from:tid_index)
                               (to:tid_index { U16.v from <= U16.v to })
                               (f:tid -> vprop)

  : Tot (vprop)
        (decreases (U16.v to - U16.v from))
  = if from = to then emp
    else f from `star`
         forall_threads_between U16.(from +^ 1us) to f

noextract
let n_threads_16 : tid_index = U16.uint_to_t (U32.v n_threads)

let forall_threads (f: tid -> vprop) =
  forall_threads_between 0us n_threads_16 f


// This creates a Zeta instance
val init (_:unit)
  : STT top_level_state
        emp
        (fun t -> core_inv t `star`
               TLM.tids_pts_to t.aeh.mlogs half (Map.const (Some Seq.empty)) false)

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
    TLM.tid_pts_to t.aeh.mlogs tid half (entries `Seq.append` entries') false
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
       exists_ (fun entries' -> TLM.tid_pts_to t.aeh.mlogs tid half entries' false))

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
     TLM.tid_pts_to t.aeh.mlogs tid half entries false)
    (verify_post t tid entries log_perm log_bytes len input out_len out_bytes output)

let max_certified_epoch (t:top_level_state)
  : STT AEH.max_certified_epoch_result emp (AEH.read_max_post t.aeh)
  = AEH.advance_and_read_max_certified_epoch t.aeh

//From this, we should connect back to the semantic
//proof and show that the entries are sequentially consistent up to eid
//except for hash collisions
