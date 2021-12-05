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

module T = Zeta.Steel.FormatsManual
module M = Zeta.Steel.ThreadStateModel
module AEH = Zeta.Steel.AggregateEpochHashes
module V = Zeta.Steel.Verifier
module SA = Zeta.SeqAux
module MR = Steel.MonotonicReference
#push-options "--ide_id_info_off"

let thread_inv (t: V.thread_state_t)
               (logref: AEH.log_ref)
  : vprop
  = exists_ (fun tsm ->
       V.thread_state_inv t tsm `star`
       G.pts_to logref half (M.committed_entries tsm))

noeq
type thread_state (logrefs:AEH.log_refs_t) =
{
  tid: tid;
  tsm: V.thread_state_t;
  logref: AEH.log_ref;
  lock : Lock.lock (thread_inv tsm logref);
  properties : squash (
    logref == Map.sel logrefs tid
  );
}

let all_threads_t logrefs =
  a:A.array (thread_state logrefs) {
      A.length a == U32.v n_threads
  }

noeq
type top_level_state = {
  logrefs : erased AEH.log_refs_t;
  all_threads : all_threads_t (reveal logrefs);
  epoch_hashes: AEH.aggregate_epoch_hashes (reveal logrefs);
}


let thread_has_processed (t:top_level_state)
                         (tid:tid)
                         (entries:AEH.log) =
    AEH.thread_has_processed t.epoch_hashes.mlogs tid entries

let all_threads_have_processed (t:top_level_state)
                               (entries:AEH.all_processed_entries) =
    AEH.all_threads_have_processed t.epoch_hashes.mlogs entries


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

// This creates a Zeta instance
val init (_:unit)
  : STT top_level_state emp core_inv

val verify_entries (t:top_level_state)
                   (tid:tid)
                   (#log_bytes:erased bytes)
                   (len: U32.t)
                   (input:larray U8.t len)
                   (out_len: U32.t)
                   (output:larray U8.t out_len)
  : STT (option U32.t) //bool & U32.t & erased (Seq.seq log_entry_base))
    (core_inv t `star`
     A.pts_to input log_bytes `star`
     exists_ (A.pts_to output))
    (fun res ->
      core_inv t `star`
      A.pts_to input log_bytes `star`
      (match res, V.parse_log log_bytes with
       | None, _ ->
         exists_ (A.pts_to output)

       | Some _, None ->
         pure False

       | Some n_out, Some entries' ->
         exists_ (fun entries -> //this is a little weak: It doesn't prevent the thread from silently adding some more entries to the log
                              //we could give a 1/4 permission to the logref to the client to allow them to correlate the initial
                              //state, rather than just existentially quantifying it here
         exists_ (fun out_bytes ->
           A.pts_to output out_bytes `star`
           pure (
             let tsm0 = M.verify_model (M.init_thread_state_model tid) entries in
             let tsm1 = M.verify_model tsm0 entries' in
             out_bytes == M.bytes_of_app_results (M.delta_app_results tsm0 tsm1) /\
             U32.v n_out == Seq.length out_bytes /\
             thread_has_processed t tid (entries `Seq.append` entries'))))))

val max_certified_epoch (logs:erased AEH.all_processed_entries)
                        (t:top_level_state)
  : ST M.epoch_id
    (core_inv t)
    (fun _ -> core_inv t)
    (requires all_threads_have_processed t logs)
    (ensures fun max ->
      forall (eid:M.epoch_id).
         U32.v eid <= U32.v max ==>
         M.epoch_is_certified logs eid)

//From this, we should connect back to the semantic
//proof and show that the entries are sequentially consistent up to eid
//except for hash collisions
