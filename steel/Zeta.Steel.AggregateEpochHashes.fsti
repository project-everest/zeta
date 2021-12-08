module Zeta.Steel.AggregateEpochHashes

open FStar.Ghost
open Steel.ST.Util
module A = Steel.ST.Array
module R = Steel.ST.Reference
module G = Steel.ST.GhostReference
module Lock = Steel.ST.SpinLock
open Zeta.Steel.ApplicationTypes
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
open Zeta.Steel.FormatsManual
module IArray = Zeta.Steel.IArray
module T = Zeta.Steel.FormatsManual
module M = Zeta.Steel.ThreadStateModel
module HA = Zeta.Steel.HashAccumulator
open Zeta.Steel.Util
module MR = Steel.ST.MonotonicReference
module GMap = Zeta.Steel.GhostSharedMap
#push-options "--ide_id_info_off"

/// Initializer for an IArray
val epoch_hash_size : U32.t

noeq
type epoch_hashes_t = {
  hadd: HA.ha;
  hevict: HA.ha;
}

let epoch_hashes_repr = IArray.repr M.epoch_id M.epoch_hash
let epoch_id_hash (x:M.epoch_id) : U32.t = x
let epoch_hash_perm (k:M.epoch_id)
                    (v:epoch_hashes_t)
                    (c:M.epoch_hash) =
    HA.ha_val v.hadd c.hadd `star`
    HA.ha_val v.hevict c.hevict

let all_epoch_hashes =
  IArray.tbl
    #M.epoch_id
    #epoch_hashes_t
    #M.epoch_hash
    epoch_id_hash
    epoch_hash_perm

let tid_bitmap = Seq.lseq bool (U32.v n_threads)
let epoch_tid_bitmaps =
  IArray.tbl
    #M.epoch_id
    #(larray bool n_threads)
    #tid_bitmap
    epoch_id_hash
    (fun i -> A.pts_to)

let is_epoch_verified (eid:M.epoch_id) (lve:M.epoch_id) =
  U32.v lve >= U32.v eid

[@@erasable]
let epoch_hash_contributions_t =
  erased (Seq.lseq epoch_hashes_repr (U32.v n_threads))

let thread_contribs (contribs:epoch_hash_contributions_t) (tid:tid) =
  Seq.index contribs (U16.v tid)

let upd_thread_contribs (contribs:epoch_hash_contributions_t)
                        (tid:tid)
                        (v:_) =
  Seq.upd contribs (U16.v tid) v

let aggregate_epoch_hash (e0 e1:M.epoch_hash)
  : M.epoch_hash
  = { hadd = HA.aggregate_hashes e0.hadd e1.hadd;
      hevict = HA.aggregate_hashes e0.hevict e1.hevict}

let aggregate_thread_epoch_hashes (e:M.epoch_id)
                                  (contribs:epoch_hash_contributions_t)
  : M.epoch_hash
  = Zeta.SeqAux.reduce M.init_epoch_hash
                       (fun (s:epoch_hashes_repr) -> aggregate_epoch_hash (Map.sel s e))
                       contribs

let frame_aggregate_thread_epoch_hashes (e e':M.epoch_id)
                                        (contribs:epoch_hash_contributions_t)
                                        (tid:tid)
                                        (v:M.epoch_hash)
  : Lemma (requires e <> e')
          (ensures (
            let tid = U16.v tid in
            aggregate_thread_epoch_hashes e contribs ==
            aggregate_thread_epoch_hashes e (Seq.upd contribs tid (Map.upd (Seq.index contribs tid) e' v))))
  = admit()


(* Global monotonic log of entries *)
let log = Seq.seq log_entry_base
let all_processed_entries = Seq.lseq log (U32.v n_threads)
let map_of_seq (a:all_processed_entries)
  : Map.t tid log
  = map_literal (fun (tid:tid) -> Seq.index a (U16.v tid))

let log_of_tid (a:all_processed_entries) (t:tid) = Seq.index a (U16.v t)
let log_grows :Preorder.preorder log
  = let open FStar.Seq in
    fun (s1 s2:log) ->
      length s1 <= length s2 /\
      (forall (i:nat).{:pattern (Seq.index s1 i) \/ (Seq.index s2 i)}
         i < length s1 ==> index s1 i == index s2 i)

let all_logs_grow
  : Preorder.preorder all_processed_entries
  = fun (m0 m1:all_processed_entries) ->
       forall tid. log_grows (log_of_tid m0 tid) (log_of_tid m1 tid)

let committed_tsm_of_logs (mlogs_v:all_processed_entries) (t:tid) =
   M.verify_model (M.init_thread_state_model t)
                  (M.committed_log_entries (log_of_tid mlogs_v t))

let thread_contrib_of_log (t:tid) (l:log)
  : epoch_hashes_repr
  = let tsm = M.verify_model (M.init_thread_state_model t) l in
    Zeta.Steel.Util.map_literal
      (fun (e:M.epoch_id) ->
         if is_epoch_verified e tsm.last_verified_epoch
         then Map.sel tsm.epoch_hashes e
         else M.init_epoch_hash)

let contribs_of_logs (mlogs_v:all_processed_entries)
  : epoch_hash_contributions_t
  = Zeta.SeqAux.mapi mlogs_v
                     (fun tid -> thread_contrib_of_log (U16.uint_to_t tid) (Seq.index mlogs_v tid))

let all_contributions_are_accurate (global:epoch_hashes_repr)
                                   (mlogs_v:all_processed_entries)
  : prop
  = forall (e:M.epoch_id). Map.sel global e == aggregate_thread_epoch_hashes e (contribs_of_logs mlogs_v)

let max_certified_epoch_is (global:epoch_hashes_repr)
                           (bitmaps: IArray.repr M.epoch_id tid_bitmap)
                           (max:M.epoch_id)
  : prop
  = forall (e:M.epoch_id).
       U32.v e <= U32.v max ==>
       (Map.sel bitmaps e) == Seq.create (U32.v n_threads) true /\
       (Map.sel global e).hadd == (Map.sel global e).hevict

let contribs_and_max_ok (global:epoch_hashes_repr)
                        (bitmaps: IArray.repr M.epoch_id tid_bitmap)
                        (max:M.epoch_id)
                        (mlogs_v:all_processed_entries)
 : prop
 = all_contributions_are_accurate global mlogs_v /\
   max_certified_epoch_is global bitmaps max

let tid_index = i:U16.t { U16.v i <= U32.v n_threads }

noextract
let n_threads_16 : tid_index = U16.uint_to_t (U32.v n_threads)

let rec forall_threads_between (from:tid_index)
                               (to:tid_index { U16.v from <= U16.v to })
                               (f:tid -> vprop)

  : Tot (vprop)
        (decreases (U16.v to - U16.v from))
  = if from = to then emp
    else f from `star`
         forall_threads_between U16.(from +^ 1us) to f

let forall_threads (f: tid -> vprop) =
  forall_threads_between 0us n_threads_16 f

let per_thread_max_and_bitmap (max:M.epoch_id)
                              (bitmaps: IArray.repr M.epoch_id tid_bitmap)
                              (tid:tid)
                              (all_logs:all_processed_entries)
  : prop
  = let tsm = M.verify_model (M.init_thread_state_model tid) (log_of_tid all_logs tid) in
    U32.v max <= U32.v tsm.last_verified_epoch /\ //max can't exceed the verified epoch ctr for tid
    (forall (eid:M.epoch_id).
      Seq.index (Map.sel bitmaps eid) (U16.v tid) == is_epoch_verified eid tsm.last_verified_epoch)

let per_thread_invariant (max:_)
                         (bitmaps:_)
                         (all_logs: all_processed_entries)
                         ([@@@smt_fallback] tid:tid) =
    pure (per_thread_max_and_bitmap max bitmaps tid all_logs)

val take_thread (#o:_) (#p:tid -> vprop) (i:tid)
  : STGhostT unit o
    (forall_threads p)
    (fun _ -> p i `star`
         forall_threads_between 0us i p `star`
         forall_threads_between U16.(i +^ 1us) n_threads_16 p)

val put_thread (#o:_) (#p:tid -> vprop) (i:tid)
  : STGhostT unit o
    (p i `star`
     forall_threads_between 0us i p `star`
     forall_threads_between U16.(i +^ 1us) n_threads_16 p)
    (fun _ -> forall_threads p)

let refined_tid (p:tid -> Type0) = t:tid{p t}

val update_forall_thread_between (#o:_)
                                 (#p #q:tid -> vprop) (#refine:tid -> Type0)
                                 (i:tid_index)
                                 (j:tid_index{U16.v i <= U16.v j})
                                 ($f: (k:refined_tid refine -> STGhostT unit o (p k) (fun _-> q k)))
  : STGhost unit o
     (forall_threads_between i j p)
     (fun _ -> forall_threads_between i j q)
     (requires (forall k. U16.v i <= U16.v k /\ U16.v k < U16.v j ==> refine k))
     (ensures fun _ -> True)


let monotonic_logs = GMap.t tid log log_grows


[@@__reduce__]
let lock_inv_body (hashes : all_epoch_hashes)
                  (tid_bitmaps : epoch_tid_bitmaps)
                  (max_certified_epoch : R.ref M.epoch_id)
                  (mlogs:monotonic_logs)
                  (hashes_v:_)
                  (bitmaps:_)
                  (max:_)
                  (mlogs_v:all_processed_entries)
  = IArray.perm hashes hashes_v Set.empty `star`
    IArray.perm tid_bitmaps bitmaps Set.empty `star`
    R.pts_to max_certified_epoch full max `star`
    GMap.global_snapshot mlogs (map_of_seq mlogs_v) `star`
    forall_threads (per_thread_invariant max bitmaps mlogs_v) `star`
    pure (contribs_and_max_ok hashes_v bitmaps max mlogs_v)

let lock_inv (hashes : all_epoch_hashes)
             (tid_bitmaps : epoch_tid_bitmaps)
             (max_certified_epoch : R.ref M.epoch_id)
             (mlogs: monotonic_logs)
 : vprop
 = exists_ (fun hashes_v ->
   exists_ (fun bitmaps ->
   exists_ (fun max ->
   exists_ (fun (mlogs_v:all_processed_entries) ->
     lock_inv_body hashes tid_bitmaps max_certified_epoch mlogs
                   hashes_v bitmaps max mlogs_v))))

noeq
type aggregate_epoch_hashes = {
     hashes : all_epoch_hashes;
     tid_bitmaps : epoch_tid_bitmaps;
     max_certified_epoch : R.ref M.epoch_id;
     mlogs: monotonic_logs;
     lock: cancellable_lock (lock_inv hashes tid_bitmaps max_certified_epoch mlogs)
}

let all_threads_have_processed (mlogs:monotonic_logs) (logs:all_processed_entries)
  : vprop
  = GMap.global_snapshot mlogs (map_of_seq logs)

let max_certified_epoch (logs:erased all_processed_entries)
                        (aeh:aggregate_epoch_hashes)
  : ST M.epoch_id
      (all_threads_have_processed aeh.mlogs logs)
      (fun _ -> all_threads_have_processed aeh.mlogs logs)
      (requires True)
      (ensures fun max ->
            forall (eid:M.epoch_id).
              U32.v eid <= U32.v max ==>
              M.epoch_is_certified logs eid)
  = admit__()
