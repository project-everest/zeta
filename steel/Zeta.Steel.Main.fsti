module Zeta.Steel.Main
open FStar.Ghost
open Zeta.Steel.ApplicationTypes
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
open Zeta.Steel.FormatsManual
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
open Steel.Array

module T = Zeta.Steel.FormatsManual
module M = Zeta.Steel.ThreadStateModel
module A = Steel.Array
module AEH = Zeta.Steel.AggregateEpochHashes
module V = Zeta.Steel.Verifier
module Lock = Steel.SpinLock
module SA = Zeta.SeqAux
module MR = Steel.MonotonicReference
#push-options "--ide_id_info_off"
val thread_state_pts_to (t:V.thread_state_t)
                        (tsm:M.thread_state_model)
  : vprop

let grows (#a:Type) :Preorder.preorder (erased (Seq.seq a))
  = let open FStar.Seq in
    fun (s1 s2:erased (seq a)) ->
      length s1 <= length s2 /\
      (forall (i:nat).{:pattern (Seq.index s1 i) \/ (Seq.index s2 i)}
         i < length s1 ==> index s1 i == index s2 i)

let log = Seq.seq log_entry_base
let elog = erased log

/// This should be a MR.ghost_ref
let monotonic_log_t = MR.ref elog grows

let mlog_refs_t = Map.t thread_id monotonic_log_t

let thread_inv (t: V.thread_state_t)
               (logref: AEH.log_ref)
               (mlogref: monotonic_log_t)
  : vprop
  = h_exists (fun (tsm, committed_entries) ->
       thread_state_pts_to t tsm `star`
       ghost_pts_to logref AEH.half committed_entries `star`
       MR.pts_to mlogref AEH.half tsm.M.processed_entries `star`
       pure (V.committed_prefix tsm.M.processed_entries committed_entries))

noeq
type thread_state (logrefs:AEH.log_refs_t)
                  (mlogrefs:mlog_refs_t) =
{
  tid: tid;
  tsm: V.thread_state_t;
  logref: AEH.log_ref;
  mlogref: monotonic_log_t;
  lock : Lock.lock (thread_inv tsm logref mlogref);
  properties : squash (
    logref == Map.sel logrefs tid /\
    mlogref == Map.sel mlogrefs tid
  );
}

let all_threads_t logrefs mlogrefs =
  a:A.array (thread_state logrefs mlogrefs) {
      A.length a == U32.v n_threads
  }

noeq
type top_level_state = {
  logrefs : erased AEH.log_refs_t;
  mlogrefs : erased mlog_refs_t; //should be erased
  all_threads : all_threads_t logrefs mlogrefs;
  epoch_hashes: AEH.aggregate_epoch_hashes logrefs;
}

val array_pts_to (#t:Type0)
                 (a:A.array t)
                 (p:Steel.FractionalPermission.perm)
                 (v:Seq.lseq t (A.length a))
  : vprop

let tid_positions_ok #l #m (all_threads: Seq.seq (thread_state l m))
  : prop
  = forall (i:SA.seq_index all_threads).
        let si = Seq.index all_threads i in
        U16.v si.tid == i

let core_inv (t:top_level_state)
  : vprop
  = h_exists (fun (perm, v) ->
      array_pts_to t.all_threads perm v `star`
      pure (tid_positions_ok v))

let initial_inv (t:top_level_state)
  : vprop
  = core_inv t `star`
    AEH.h_forall (fun (tid:thread_id) ->
      if Map.contains t.mlogrefs tid
      then MR.pts_to (Map.sel t.mlogrefs tid) AEH.half Seq.empty
      else emp)

// This creates a Zeta instance
val init (_:unit)
  : SteelT top_level_state
    emp
    initial_inv

val verify_entries (t:top_level_state)
                   (tid:thread_id)
                   (len: U32.t) (input:A.array U8.t { A.length input == U32.v len })
                   (out_len: U32.t) (output:A.array U8.t { A.length output == U32.v out_len })
                   (entries:erased (Seq.seq log_entry_base))
                   (mlogref:monotonic_log_t)
  : Steel (bool & U32.t & erased (Seq.seq log_entry_base))
    (core_inv t `star`
     A.varray input `star`
     A.varray output `star`
     MR.pts_to mlogref AEH.half entries)
    (fun res ->
      core_inv t `star`
      A.varray input `star`
      A.varray output `star`
      MR.pts_to mlogref AEH.half (let _, _, e = res in e))
    (requires fun _ ->
      Map.sel t.mlogrefs tid == mlogref)
    (ensures fun h0 (b, n, e) h1 ->
      let out_bytes = A.asel output h1 in
      if b
      then match V.spec_parser_log (A.asel input h0) with
           | Some (entries', _) ->
             let tsm0 = M.verify_model (M.init_thread_state_model tid) entries in
             let tsm1 = M.verify_model tsm0 entries' in
             e == hide (Seq.append entries entries') /\
             V.serialized_new_app_results tsm0.app_results tsm1.app_results n out_bytes
           | _ ->
             True
      else True)

let prefix_of (#a:Type) (s0 s1:Seq.seq a)
  : prop
  = let open FStar.Seq in
    length s0 <= length s1 /\
    Seq.slice s1 0 (length s0) == s0

let snapshot (r:monotonic_log_t) (s:log) =
  MR.witnessed r (fun s' -> prefix_of s s')

let run_threads (logs:(Map.t tid log)) (tid:tid)
  : M.thread_state_model
  = M.verify_model (M.init_thread_state_model tid) (Map.sel logs tid)

let tid_logs (a:M.all_logs) (tid:tid) =
  Seq.index a (U16.v tid)

val max_certified_epoch (t:top_level_state)
                        (all_logs: erased M.all_logs)
  : Steel M.epoch_id
    (core_inv t)
    (fun _ -> core_inv t)
    (requires fun _ ->
      forall (tid:tid). let lr_i = Map.sel t.mlogrefs tid in
                   snapshot lr_i (tid_logs all_logs tid))
    (ensures fun _ max _ ->
      forall (eid:M.epoch_id).
         U32.v eid <= U32.v max ==>
         M.epoch_is_certified all_logs eid)
//From this, we should connect back to the semantic
//proof and show that the entries are sequentially consistent up to eid
//except for hash collisions
