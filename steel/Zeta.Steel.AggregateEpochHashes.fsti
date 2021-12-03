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
#push-options "--ide_id_info_off"

/// Initializer for an IArray
val epoch_hash_size : U32.t

let log_ref = G.ref (Seq.seq log_entry_base)
let log_refs_t = erased (Map.t tid log_ref)

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

let epoch_hash_contributions_t = Seq.lseq epoch_hashes_repr (U32.v n_threads)

let aggregate_epoch_hash (e0 e1:M.epoch_hash)
  : M.epoch_hash
  = { hadd = HA.aggregate_hashes e0.hadd e1.hadd;
      hevict = HA.aggregate_hashes e0.hevict e1.hevict}

let aggregate_thread_epoch_hashes (e:M.epoch_id) (contribs:epoch_hash_contributions_t)
  : M.epoch_hash
  = Zeta.SeqAux.reduce M.init_epoch_hash
                       (fun s -> aggregate_epoch_hash (Map.sel s e))
                       contribs

let all_contributions_are_accurate (global:epoch_hashes_repr)
                                   (contribs:epoch_hash_contributions_t)
  : prop
  = forall (e:M.epoch_id). Map.sel global e == aggregate_thread_epoch_hashes e contribs


let max_certified_epoch_is (_:epoch_hashes_repr)
                           (_:M.epoch_id)
  : prop
  = True //TODO


let per_thread_contribution_is_accurate (max:M.epoch_id)
                                        (bitmaps: IArray.repr M.epoch_id tid_bitmap)
                                        (tid:tid)
                                        (entries:Seq.seq log_entry_base)
                                        (contribs:epoch_hashes_repr)
  : prop
  = let tsm = M.verify_model (M.init_thread_state_model tid) entries in
    U32.v max <= U32.v tsm.last_verified_epoch /\ //max can't exceed the verified epoch ctr for tid
    (forall (eid:M.epoch_id).
      let h_contrib = Map.sel contribs eid in
      let h_tsm = Map.sel tsm.epoch_hashes eid in
      Seq.index (Map.sel bitmaps eid) (U16.v tid) == is_epoch_verified eid tsm.last_verified_epoch /\
      (if is_epoch_verified eid tsm.last_verified_epoch
       then h_contrib == h_tsm
       else h_contrib == M.init_epoch_hash))

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


let thread_contribs (contribs:epoch_hash_contributions_t) (tid:tid) =
  Seq.index contribs (U16.v tid)

let upd_thread_contribs (contribs:epoch_hash_contributions_t)
                        (tid:tid)
                        (v:_) =
  Seq.upd contribs (U16.v tid) v

let per_thread_invariant (log_refs:log_refs_t)
                         (max:_)
                         (bitmaps:_)
                         (contribs:epoch_hash_contributions_t)
                         ([@@@smt_fallback] tid:tid) =
    let logref = Map.sel log_refs tid in
    let t_contribs = thread_contribs contribs tid in
    exists_ (fun (entries:_) ->
      G.pts_to logref half entries `star`
      pure (per_thread_contribution_is_accurate max bitmaps tid entries t_contribs))

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

[@@__reduce__]
let lock_inv_body (log_refs:log_refs_t)
                  (hashes : all_epoch_hashes)
                  (tid_bitmaps : epoch_tid_bitmaps)
                  (max_certified_epoch : R.ref M.epoch_id)
                  (contributions: G.ref epoch_hash_contributions_t)
                  (hashes_v:_)
                  (bitmaps:_)
                  (max:_)
                  (contributions_v:_)
  = IArray.perm hashes hashes_v Set.empty `star`
    IArray.perm tid_bitmaps bitmaps Set.empty `star`
    R.pts_to max_certified_epoch full max `star`
    G.pts_to contributions full contributions_v `star`
    pure (all_contributions_are_accurate hashes_v contributions_v /\
          max_certified_epoch_is hashes_v max) `star`
    forall_threads (per_thread_invariant log_refs max bitmaps contributions_v)

let lock_inv (log_refs:log_refs_t)
             (hashes : all_epoch_hashes)
             (tid_bitmaps : epoch_tid_bitmaps)
             (max_certified_epoch : R.ref M.epoch_id)
             (contributions: G.ref epoch_hash_contributions_t)
 : vprop
 = exists_ (fun hashes_v ->
   exists_ (fun bitmaps ->
   exists_ (fun max ->
   exists_ (fun contributions_v ->
     lock_inv_body log_refs hashes tid_bitmaps max_certified_epoch contributions
                   hashes_v bitmaps max contributions_v))))

noeq
type aggregate_epoch_hashes (log_refs:log_refs_t) = {
     hashes : all_epoch_hashes;
     tid_bitmaps : epoch_tid_bitmaps;
     max_certified_epoch : R.ref M.epoch_id;
     contributions: G.ref epoch_hash_contributions_t;
     lock: cancellable_lock (lock_inv log_refs hashes tid_bitmaps max_certified_epoch contributions)
}
