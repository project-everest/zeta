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
let log_refs_t = erased (Map.t thread_id log_ref)

noeq
type epoch_hashes_t = {
  hadd: HA.ha;
  hevict: HA.ha;
}

let epoch_hashes_repr = IArray.repr M.epoch_id M.epoch_hash
let epoch_id_hash (x:M.epoch_id) : U32.t = x
let epoch_hash_perm (k:M.epoch_id) (v:epoch_hashes_t) (c:M.epoch_hash) =
    HA.ha_val v.hadd c.hadd `star`
    HA.ha_val v.hevict c.hevict

let all_epoch_hashes =
  IArray.tbl
    #M.epoch_id
    #epoch_hashes_t
    #M.epoch_hash
    epoch_id_hash
    epoch_hash_perm

let is_epoch_verified (eid:M.epoch_id) (lve:option M.epoch_id) =
  match lve with
  | None -> false
  | Some eid' -> U32.v eid' >= U32.v eid

let epoch_hash_contributions_t = Map.t (thread_id & M.epoch_id) M.epoch_hash

let all_contributions_are_accurate (_:epoch_hashes_repr)
                                   (_:epoch_hash_contributions_t)
  : prop
  = True //TODO

let max_certified_epoch_is (_:epoch_hashes_repr)
                           (_:M.epoch_id)
  : prop
  = True //TODO


let per_thread_contribution_is_accurate (max:M.epoch_id)
                                        (tid:thread_id)
                                        (entries:Seq.seq log_entry_base)
                                        (contribs:epoch_hash_contributions_t)
  : prop
  = let tsm = M.verify_model (M.init_thread_state_model tid) entries in
    (match tsm.last_verified_epoch with
     | None -> max = 0ul //should max be an option too?
     | Some e -> U32.v max <= U32.v e //max can't exceed the verified epoch ctr for tid
     ) /\
    (forall (eid:M.epoch_id).
      let h_contrib = Map.sel contribs (tid, eid) in
      let h_tsm = Map.sel tsm.epoch_hashes eid in
      if is_epoch_verified eid tsm.last_verified_epoch
      then h_contrib == h_tsm
      else h_contrib == M.init_epoch_hash)


let rec forall_threads_between (tid:thread_id)
                               (down_to:thread_id { U16.v tid >= U16.v down_to })
                               (f:thread_id -> vprop)
  : Tot (vprop)
        (decreases (U16.v tid))
  = f tid `star`
    (if tid = down_to then emp
     else forall_threads_between U16.(tid -^ 1us) down_to f)

let forall_threads (f:thread_id -> vprop) =
  forall_threads_between
    (UInt16.uint_to_t (U32.v n_threads))
    0us
    f


let lock_inv (log_refs:log_refs_t)
             (hashes : all_epoch_hashes)
             (max_certified_epoch : R.ref M.epoch_id)
             (contributions: G.ref epoch_hash_contributions_t)
 : vprop
 = exists_ (fun hashes_v ->
   exists_ (fun max ->
   exists_ (fun contributions_v ->
      IArray.perm hashes hashes_v Set.empty `star`
      R.pts_to max_certified_epoch full max `star`
      G.pts_to contributions full contributions_v `star`
      pure (all_contributions_are_accurate hashes_v contributions_v /\
            max_certified_epoch_is hashes_v max) `star`
      forall_threads (fun (tid:thread_id) ->
        let logref = Map.sel log_refs tid in
        exists_ (fun (entries:_) ->
            G.pts_to logref half entries `star`
            pure (per_thread_contribution_is_accurate max tid entries contributions_v))
      ))))

noeq
type aggregate_epoch_hashes (log_refs:log_refs_t) = {
     hashes : all_epoch_hashes;
     max_certified_epoch : R.ref M.epoch_id;
     contributions: G.ref epoch_hash_contributions_t;
     lock: Lock.lock (lock_inv log_refs hashes max_certified_epoch contributions)
}
