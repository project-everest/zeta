module Zeta.Steel.AggregateEpochHashes

open FStar.Ghost
open Steel.ST.Util
module A = Steel.ST.Array
module R = Steel.ST.Reference
module G = Steel.ST.GhostReference
module Lock = Steel.ST.CancellableSpinLock
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

let tid_bitmap = Seq.lseq bool (U32.v n_threads)
let epoch_hashes_repr = EpochMap.repr M.epoch_hash
let epoch_bitmaps_repr = EpochMap.repr tid_bitmap

let all_epoch_hashes = EpochMap.tbl epoch_hash_perm

let epoch_tid_bitmaps =
  EpochMap.tbl #(larray bool n_threads)
               #tid_bitmap
               (fun i -> array_pts_to)

let is_epoch_verified (tsm:M.thread_state_model) (eid:M.epoch_id) =
  not tsm.failed &&
  not (M.epoch_greater_than_last_verified_epoch tsm.last_verified_epoch eid)

let all_threads_epoch_hashes =
  Seq.lseq epoch_hashes_repr (U32.v n_threads)

let aggregate_epoch_hash (e0 e1:M.epoch_hash)
  : M.epoch_hash
  = { hadd = HA.aggregate_hashes e0.hadd e1.hadd;
      hevict = HA.aggregate_hashes e0.hevict e1.hevict}

let aggregate_epoch_hash_unit (i:M.epoch_hash)
  : Lemma (aggregate_epoch_hash M.init_epoch_hash i == i)
          [SMTPat (aggregate_epoch_hash M.init_epoch_hash i)]
  = HA.initial_hash_unit i.hadd;
    HA.initial_hash_unit i.hevict

let aggregate_epoch_hash_comm (i j:M.epoch_hash)
  : Lemma (aggregate_epoch_hash i j == aggregate_epoch_hash j i)
  = HA.aggregate_hashes_commutative i.hadd j.hadd;
    HA.aggregate_hashes_commutative i.hevict j.hevict

let aggregate_epoch_hash_assoc (i j k:M.epoch_hash)
  : Lemma (aggregate_epoch_hash (aggregate_epoch_hash i j) k ==
           aggregate_epoch_hash i (aggregate_epoch_hash j k))
  = HA.aggregate_hashes_associative i.hadd j.hadd k.hadd;
    HA.aggregate_hashes_associative i.hevict j.hevict k.hevict

module CE = FStar.Algebra.CommMonoid.Equiv

let aggregate_epoch_hash_equiv 
  : CE.equiv M.epoch_hash 
  = CE.EQ ( == ) (fun _ -> ()) (fun _ _ -> ()) (fun _ _ _ -> ())
let aggregate_epoch_hash_monoid
  : CE.cm M.epoch_hash aggregate_epoch_hash_equiv
  = CE.CM M.init_epoch_hash
       aggregate_epoch_hash
       aggregate_epoch_hash_unit
       aggregate_epoch_hash_assoc
       aggregate_epoch_hash_comm
       (fun _ _ _ _ -> ())

let log = Seq.seq log_entry

let tid_logs = Seq.seq (tid & log)

let maybe_log_of_tid (l:tid_logs) (t:tid)
  : option (tid & log)
  = Seq.find_r (fun (t', _) -> t' = t) l
  
let all_tid_logs = Seq.lseq (tid & log) (U32.v n_threads)
    
let thread_contrib_of_log (t:tid) (l:log)
  : epoch_hashes_repr
  = let tsm = M.verify_model (M.init_thread_state_model t) l in
    FStar.Map.map_literal
      (fun (e:M.epoch_id) ->
         if is_epoch_verified tsm e
         then Map.sel tsm.epoch_hashes e
         else M.init_epoch_hash)

let all_threads_epoch_hashes_of_logs (mlogs_v:Seq.seq (tid & log))
  : mlogs_v':Seq.seq epoch_hashes_repr { Seq.length mlogs_v' == Seq.length mlogs_v }
  = Zeta.SeqAux.map (fun tid_l -> thread_contrib_of_log (fst tid_l) (snd tid_l)) mlogs_v
                   
let aggregate_epoch_hashes_seq (epoch_hashes:Seq.seq M.epoch_hash)
  : M.epoch_hash
  = FStar.Seq.Permutation.foldm_snoc aggregate_epoch_hash_monoid epoch_hashes

let aggregate_all_threads_epoch_hashes (e:M.epoch_id)
                                       (mlogs_v:Seq.seq (tid & log))
  : M.epoch_hash
  = aggregate_epoch_hashes_seq (Zeta.SeqAux.map (fun (s:epoch_hashes_repr) -> Map.sel s e)
                                                (all_threads_epoch_hashes_of_logs mlogs_v))

let split_tid (mlogs_v:Seq.lseq 'a (U32.v n_threads))
              (t:tid)
  = let prefix= Seq.slice mlogs_v 0 (U16.v t) in
    let suffix = Seq.slice mlogs_v (U16.v t + 1) (U32.v n_threads) in
    prefix, Seq.index mlogs_v (U16.v t), suffix

let aggregate_all_threads_epoch_hashes_seq_permute (ehs:Seq.lseq M.epoch_hash (U32.v n_threads))
                                                   (t:tid)
  : Lemma (
      let prefix, et, suffix = split_tid ehs t in
      aggregate_epoch_hashes_seq ehs ==
      aggregate_epoch_hash et (aggregate_epoch_hashes_seq (Seq.append prefix suffix)))
  = let open FStar.Seq.Permutation in
    let seq_lhs = ehs in
    let seq_prefix, i, seq_suffix = split_tid seq_lhs t in
    let seq_rhs = Seq.snoc (Seq.append seq_prefix seq_suffix) i in
    let permutation_fun
      : index_fun seq_lhs
      = fun l -> 
          if l < U16.v t
          then l
          else if l > U16.v t
          then l - 1
          else Seq.length seq_lhs - 1
    in
    FStar.Seq.Permutation.reveal_is_permutation seq_lhs seq_rhs permutation_fun;
    assert (is_permutation seq_lhs seq_rhs permutation_fun);
    FStar.Seq.Permutation.foldm_snoc_perm aggregate_epoch_hash_monoid seq_lhs seq_rhs permutation_fun;
    assert (aggregate_epoch_hashes_seq seq_lhs == aggregate_epoch_hashes_seq seq_rhs);
    let s, last = Seq.un_snoc seq_rhs in
    Seq.un_snoc_snoc (Seq.append seq_prefix seq_suffix) i;
    assert (s `Seq.equal` Seq.append seq_prefix seq_suffix); ()

let rec all_threads_epoch_hashes_of_logs_append (mlogs_v mlogs_v':Seq.seq (tid & log))
  : Lemma (ensures
             (all_threads_epoch_hashes_of_logs (mlogs_v `Seq.append` mlogs_v'))  `Seq.equal`
             (all_threads_epoch_hashes_of_logs mlogs_v `Seq.append` all_threads_epoch_hashes_of_logs mlogs_v'))
          (decreases (Seq.length mlogs_v'))
  = if Seq.length mlogs_v' = 0 then ()
    else (
      let prefix, last = Seq.un_snoc mlogs_v' in
      all_threads_epoch_hashes_of_logs_append mlogs_v prefix
    )


let all_processed_entries = 
    s:all_tid_logs { forall (i:nat{i < Seq.length s}). U16.v (fst (Seq.index s i)) == i }

let aggregate_all_threads_epoch_hashes_permute (e:M.epoch_id)
                                               (mlogs_v:all_processed_entries)
                                               (t:tid)
  : Lemma (
      let prefix, et, suffix = split_tid mlogs_v t in
      aggregate_all_threads_epoch_hashes e mlogs_v ==
      aggregate_epoch_hash
        (Map.sel (thread_contrib_of_log t (snd et)) e)
        (aggregate_all_threads_epoch_hashes e (Seq.append prefix suffix)))
  = let lprefix, et, lsuffix = split_tid mlogs_v t in
    let lhs = Zeta.SeqAux.map (fun (s:epoch_hashes_repr) -> Map.sel s e)
                              (all_threads_epoch_hashes_of_logs mlogs_v) in
    aggregate_all_threads_epoch_hashes_seq_permute lhs t;
    let prefix, it, suffix = split_tid lhs t in
    let f = (fun (s:epoch_hashes_repr) -> Map.sel s e) in
    let lp_ls = (Seq.append lprefix lsuffix) in
    let lmap = (Zeta.SeqAux.map f (all_threads_epoch_hashes_of_logs lp_ls)) in
    let ps = (Seq.append prefix suffix) in
    assert (Seq.equal (Zeta.SeqAux.map f (all_threads_epoch_hashes_of_logs lp_ls))
                      (Seq.append prefix suffix))

(* Global monotonic log of entries *)

let map_of_seq (a:all_processed_entries)
  : TLM.repr
  = FStar.Map.map_literal (fun (tid:tid) -> Some (snd (Seq.index a (U16.v tid))))

let log_of_tid (a:all_processed_entries) (t:tid) = snd (Seq.index a (U16.v t))
    
let tsm_of_log (mlogs_v:all_processed_entries) (t:tid) =
  M.verify_model (M.init_thread_state_model t)
                 (log_of_tid mlogs_v t)

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
                           (max:option M.epoch_id)
  : prop
  = Some? max ==>
    (forall (e:M.epoch_id).
        U32.v e <= U32.v (Some?.v max) ==>
        (Map.sel bitmaps e) == all_ones /\
        (Map.sel global e).hadd == (Map.sel global e).hevict)

let epoch_is_complete (mlogs_v:all_processed_entries) (e:M.epoch_id)
  = forall tid. is_epoch_verified (tsm_of_log mlogs_v tid) e

let per_thread_bitmap_and_max (bitmaps:epoch_bitmaps_repr)
                              (max:option M.epoch_id)
                              (all_logs:all_processed_entries)
                              (tid:tid)
  : prop
  = let tsm = M.verify_model (M.init_thread_state_model tid) (log_of_tid all_logs tid) in
    (Some? max ==> not (M.epoch_greater_than_last_verified_epoch tsm.last_verified_epoch (Some?.v max))) /\
    (forall (eid:M.epoch_id).
       Seq.index (Map.sel bitmaps eid) (U16.v tid) == is_epoch_verified tsm eid)

let hashes_bitmaps_max_ok (hashes:epoch_hashes_repr)
                          (bitmaps:epoch_bitmaps_repr)
                          (max:option (M.epoch_id))
                          (mlogs_v:all_processed_entries)
 : prop
 = all_contributions_are_accurate hashes mlogs_v /\
   max_certified_epoch_is hashes bitmaps max /\
   (forall tid. per_thread_bitmap_and_max bitmaps max mlogs_v tid)

[@@__reduce__]
let lock_inv_body (hashes : all_epoch_hashes)
                  (tid_bitmaps : epoch_tid_bitmaps)
                  (max_certified_epoch : R.ref (option M.epoch_id))
                  (mlogs:TLM.t)
                  (hashes_v:epoch_hashes_repr)
                  (bitmaps:epoch_bitmaps_repr)
                  (max:option M.epoch_id)
                  (mlogs_v:all_processed_entries)
  = EpochMap.full_perm hashes M.init_epoch_hash hashes_v `star`
    EpochMap.full_perm tid_bitmaps all_zeroes bitmaps `star`
    R.pts_to max_certified_epoch full max `star`
    TLM.global_anchor mlogs (map_of_seq mlogs_v) `star`
    pure (hashes_bitmaps_max_ok hashes_v bitmaps max mlogs_v)

[@@ __reduce__]
let lock_inv (hashes : all_epoch_hashes)
             (tid_bitmaps : epoch_tid_bitmaps)
             (max_certified_epoch : R.ref (option M.epoch_id))
             (mlogs: TLM.t)
 : vprop
 = exists_ (fun hashes_v ->
   exists_ (fun bitmaps ->
   exists_ (fun max ->
   exists_ (fun (mlogs_v:all_processed_entries) ->
     lock_inv_body hashes tid_bitmaps max_certified_epoch mlogs
                   hashes_v bitmaps max mlogs_v))))

[@@CAbstractStruct]
noeq
type aggregate_epoch_hashes = {
  hashes : all_epoch_hashes;
  tid_bitmaps : epoch_tid_bitmaps;
  max_certified_epoch : R.ref (option M.epoch_id);
  mlogs: TLM.t;
  lock: Lock.cancellable_lock (lock_inv hashes tid_bitmaps max_certified_epoch mlogs)
}

val create (_:unit)
  : STT aggregate_epoch_hashes
        emp
        (fun aeh -> TLM.tids_pts_to aeh.mlogs full_perm (Map.const (Some Seq.empty)) false)

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

val release_lock (#hv:erased epoch_hashes_repr)
                 (#bitmaps:erased epoch_bitmaps_repr)
                 (#max:erased _)
                 (#mlogs_v:erased _)
                 (#hashes : all_epoch_hashes)
                 (#tid_bitmaps : epoch_tid_bitmaps)
                 (#max_certified_epoch : R.ref (option M.epoch_id))
                 (#mlogs: TLM.t)
                 (lock: Lock.cancellable_lock
                        (lock_inv hashes tid_bitmaps max_certified_epoch mlogs))
  : STT unit
    (lock_inv_body hashes tid_bitmaps max_certified_epoch mlogs
                       hv bitmaps max mlogs_v `star`
     Lock.can_release lock)
    (fun _ -> emp)

type max_certified_epoch_result =
  | Read_max_error : max_certified_epoch_result
  | Read_max_none  : max_certified_epoch_result
  | Read_max_some  : M.epoch_id -> max_certified_epoch_result

[@@ __reduce__]
let read_max_post_pred (aeh:aggregate_epoch_hashes) (max:M.epoch_id)
  : all_processed_entries -> vprop
  = fun logs ->
    TLM.global_snapshot aeh.mlogs (map_of_seq logs)
      `star`
    pure (max_is_correct logs max)

let read_max_post (aeh:aggregate_epoch_hashes)
  : post_t max_certified_epoch_result
  = fun r ->
    match r with
    | Read_max_error  //underspec: overflow or element went missing in IArray
    | Read_max_none -> emp  //no epoch has been certified yet
    | Read_max_some max -> exists_ (read_max_post_pred aeh max)

val advance_and_read_max_certified_epoch (aeh:aggregate_epoch_hashes)
  : STT max_certified_epoch_result emp (read_max_post aeh)
