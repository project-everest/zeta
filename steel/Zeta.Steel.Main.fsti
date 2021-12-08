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
module GMap = Zeta.Steel.GhostSharedMap

module T = Zeta.Steel.FormatsManual
module M = Zeta.Steel.ThreadStateModel
module AEH = Zeta.Steel.AggregateEpochHashes
module V = Zeta.Steel.Verifier
module SA = Zeta.SeqAux
#push-options "--ide_id_info_off"

let thread_inv (t: V.thread_state_t)
               (mlogs: AEH.monotonic_logs)
  : vprop
  = exists_ (fun tsm ->
       V.thread_state_inv t tsm `star`
       GMap.owns_key mlogs tsm.M.thread_id half tsm.M.processed_entries)

noeq
type thread_state (mlogs:AEH.monotonic_logs) =
{
  tid: tid;
  tsm: V.thread_state_t;
  lock : Lock.lock (thread_inv tsm mlogs)
}

let all_threads_t (mlogs:AEH.monotonic_logs) =
    larray (thread_state mlogs) n_threads

noeq
type top_level_state = {
  aeh: AEH.aggregate_epoch_hashes;
  all_threads : all_threads_t aeh.mlogs
}


/// TODO: a fractional permission variant of Steel.ST.Array
val array_pts_to (#t:Type0)
                 (a:A.array t)
                 (p:Steel.FractionalPermission.perm)
                 (v:Seq.seq t)
  : vprop

let tid_positions_ok #l (all_threads: Seq.seq (thread_state l))
  : prop
  = forall (i:SA.seq_index all_threads).
        let si = Seq.index all_threads i in
        U16.v si.tid == i

let core_inv (t:top_level_state)
  : vprop
  = exists_ (fun perm ->
    exists_ (fun v ->
      array_pts_to t.all_threads perm v `star`
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
               forall_threads (fun tid -> GMap.owns_key t.aeh.mlogs tid half Seq.empty))

val verify_entries (t:top_level_state)
                   (tid:tid)
                   (#entries:erased AEH.log)
                   (#log_bytes:erased bytes)
                   (len: U32.t)
                   (input:larray U8.t len)
                   (out_len: U32.t)
                   (output:larray U8.t out_len)
  : STT (option U32.t) //bool & U32.t & erased (Seq.seq log_entry_base))
    (core_inv t `star`
     A.pts_to input log_bytes `star`
     exists_ (A.pts_to output) `star`
     GMap.owns_key t.aeh.mlogs tid half entries)
    (fun res ->
      core_inv t `star`
      A.pts_to input log_bytes `star`
      (match res, V.parse_log log_bytes with
       | None, _ ->
         exists_ (A.pts_to output)

       | Some _, None ->
         pure False

       | Some n_out, Some entries' ->
         exists_ (fun out_bytes ->
           A.pts_to output out_bytes `star`
           GMap.owns_key t.aeh.mlogs tid half (entries `Seq.append` entries') `star`
           pure (
             let tsm0 = M.verify_model (M.init_thread_state_model tid) entries in
             let tsm1 = M.verify_model tsm0 entries' in
             out_bytes == M.bytes_of_app_results (M.delta_app_results tsm0 tsm1) /\
             U32.v n_out == Seq.length out_bytes))))

let max_certified_epoch (t:top_level_state)
  : STT (option M.epoch_id)
      emp
      (fun max_opt ->
        match max_opt with
        | None -> emp
        | Some max ->
          exists_ (fun logs ->
           GMap.global_snapshot t.aeh.mlogs (AEH.map_of_seq logs) `star`
           pure (AEH.max_is_correct logs max)))
  = AEH.advance_and_read_max_certified_epoch t.aeh

//From this, we should connect back to the semantic
//proof and show that the entries are sequentially consistent up to eid
//except for hash collisions
