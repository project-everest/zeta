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
module EpochMap = Zeta.Steel.EpochMap
module T = Zeta.Steel.FormatsManual
module M = Zeta.Steel.ThreadStateModel
module HA = Zeta.Steel.HashAccumulator
open Zeta.Steel.Util
module MR = Steel.ST.MonotonicReference
module TLM = Zeta.Steel.ThreadLogMap
open Zeta.Steel.EpochHashes

#push-options "--ide_id_info_off"


//AR: TODO: This val is not used anywhere?
//val epoch_hash_size : U32.t

let tid_bitmap = Seq.lseq bool (U32.v n_threads)
let epoch_hashes_repr = EpochMap.repr M.epoch_hash
let epoch_bitmaps_repr = EpochMap.repr tid_bitmap

let all_epoch_hashes = EpochMap.tbl epoch_hash_perm

let epoch_tid_bitmaps =
  EpochMap.tbl #(larray bool n_threads)
               #tid_bitmap
               (fun i -> array_pts_to)

let is_epoch_verified (tsm:M.thread_state_model) (eid:M.epoch_id) =
  U32.v tsm.M.last_verified_epoch >= U32.v eid

let all_threads_epoch_hashes =
  Seq.lseq epoch_hashes_repr (U32.v n_threads)

let aggregate_epoch_hash (e0 e1:M.epoch_hash)
  : M.epoch_hash
  = { hadd = HA.aggregate_hashes e0.hadd e1.hadd;
      hevict = HA.aggregate_hashes e0.hevict e1.hevict}

let log = Seq.seq log_entry
let all_processed_entries = Seq.lseq log (U32.v n_threads)

let tsm_of_log (mlogs_v:all_processed_entries) (t:tid) =
  M.verify_model (M.init_thread_state_model t)
                 (Seq.index mlogs_v (U16.v t))

let thread_contrib_of_log (t:tid) (l:log)
  : epoch_hashes_repr
  = let tsm = M.verify_model (M.init_thread_state_model t) l in
    Zeta.Steel.Util.map_literal
      (fun (e:M.epoch_id) ->
         if is_epoch_verified tsm e
         then Map.sel tsm.epoch_hashes e
         else M.init_epoch_hash)

let all_threads_epoch_hashes_of_logs (mlogs_v:all_processed_entries)
  : all_threads_epoch_hashes
  = Zeta.SeqAux.mapi mlogs_v
                     (fun tid -> thread_contrib_of_log (U16.uint_to_t tid) (Seq.index mlogs_v tid))

let aggregate_all_threads_epoch_hashes (e:M.epoch_id)
                                       (mlogs_v:all_processed_entries)
  : M.epoch_hash
  = Zeta.SeqAux.reduce M.init_epoch_hash
                       (fun (s:epoch_hashes_repr) -> aggregate_epoch_hash (Map.sel s e))
                       (all_threads_epoch_hashes_of_logs mlogs_v)

(* Global monotonic log of entries *)


let map_of_seq (a:all_processed_entries)
  : TLM.repr
  = FStar.Map.map_literal (fun (tid:tid) -> Some (Seq.index a (U16.v tid)))

let log_of_tid (a:all_processed_entries) (t:tid) = Seq.index a (U16.v t)

let committed_tsm_of_logs (mlogs_v:all_processed_entries) (t:tid) =
   M.verify_model (M.init_thread_state_model t)
                  (M.committed_log_entries (log_of_tid mlogs_v t))

let all_contributions_are_accurate (global:epoch_hashes_repr)
                                   (mlogs_v:all_processed_entries)
  : prop
  = forall (e:M.epoch_id). Map.sel global e == aggregate_all_threads_epoch_hashes e mlogs_v

let all_ones = Seq.create (U32.v n_threads) true
let all_zeroes = Seq.create (U32.v n_threads) false

let max_certified_epoch_is (global:epoch_hashes_repr)
                           (bitmaps:epoch_bitmaps_repr)
                           (max:M.epoch_id)
  : prop
  = forall (e:M.epoch_id).
       U32.v e <= U32.v max ==>
       (Map.sel bitmaps e) == all_ones /\
       (Map.sel global e).hadd == (Map.sel global e).hevict


let epoch_is_complete (mlogs_v:all_processed_entries) (e:M.epoch_id)
  = forall tid. is_epoch_verified (tsm_of_log mlogs_v tid) e

let per_thread_bitmap_and_max (bitmaps:epoch_bitmaps_repr)
                              (max:M.epoch_id)
                              (all_logs:all_processed_entries)
                              (tid:tid)
  : prop
  = let tsm = M.verify_model (M.init_thread_state_model tid) (log_of_tid all_logs tid) in
    U32.v max <= U32.v tsm.last_verified_epoch /\ //max can't exceed the verified epoch ctr for tid
    (forall (eid:M.epoch_id).
      Seq.index (Map.sel bitmaps eid) (U16.v tid) == is_epoch_verified tsm eid)

let hashes_bitmaps_max_ok (hashes:epoch_hashes_repr)
                          (bitmaps:epoch_bitmaps_repr)
                          (max:M.epoch_id)
                          (mlogs_v:all_processed_entries)
 : prop
 = all_contributions_are_accurate hashes mlogs_v /\
   max_certified_epoch_is hashes bitmaps max /\
   (forall tid. per_thread_bitmap_and_max bitmaps max mlogs_v tid)


[@@__reduce__]
let lock_inv_body (hashes : all_epoch_hashes)
                  (tid_bitmaps : epoch_tid_bitmaps)
                  (max_certified_epoch : R.ref M.epoch_id)
                  (mlogs:TLM.t)
                  (hashes_v:_)
                  (bitmaps:_)
                  (max:_)
                  (mlogs_v:all_processed_entries)
  = EpochMap.full_perm hashes M.init_epoch_hash hashes_v `star`
    EpochMap.full_perm tid_bitmaps all_zeroes bitmaps `star`
    R.pts_to max_certified_epoch full max `star`
    TLM.global_anchor mlogs (map_of_seq mlogs_v) `star`
    pure (hashes_bitmaps_max_ok hashes_v bitmaps max mlogs_v)

let lock_inv (hashes : all_epoch_hashes)
             (tid_bitmaps : epoch_tid_bitmaps)
             (max_certified_epoch : R.ref M.epoch_id)
             (mlogs: TLM.t)
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
     mlogs: TLM.t;
     lock: cancellable_lock (lock_inv hashes tid_bitmaps max_certified_epoch mlogs)
}

let epoch_is_certified (mlogs_v:all_processed_entries)
                       (e:M.epoch_id)
  = let hashes = aggregate_all_threads_epoch_hashes e mlogs_v in
    epoch_is_complete mlogs_v e /\
    hashes.hadd == hashes.hevict

let max_is_correct (mlogs_v:_) (max:_)
  : prop
  = forall (e:M.epoch_id).
          U32.v e <= U32.v max ==>
          epoch_is_certified mlogs_v e

val advance_and_read_max_certified_epoch (aeh:aggregate_epoch_hashes)
  : STT (option M.epoch_id)
      emp
      (fun max_opt ->
        match max_opt with
        | None -> emp //underspec: overflow or element went missing in IArray
        | Some max ->
          exists_ (fun logs ->
           TLM.global_snapshot aeh.mlogs (map_of_seq logs) `star`
           pure (max_is_correct logs max)))
