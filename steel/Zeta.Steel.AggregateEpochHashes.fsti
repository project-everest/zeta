module Zeta.Steel.AggregateEpochHashes

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
module IArray = Steel.Hashtbl
module T = Zeta.Steel.FormatsManual
module M = Zeta.Steel.ThreadStateModel
module A = Steel.Array
module Lock = Steel.SpinLock
module HA = Zeta.Steel.HashAccumulator
#push-options "--ide_id_info_off"

val epoch_hash_size : U32.t

let log_ref = ghost_ref (Seq.seq log_entry_base)

let log_refs_t = Map.t thread_id log_ref

let hash_value = u256 & U64.t
let zero_hash : HA.hash_value_t = admit()
let related_hashes (h:hash_value) (h':HA.hash_value_t) = True // TODO

noeq
type epoch_hash_t = {
  hadd: hash_value;
  hevict: hash_value;
  certified: bool;
}

let related (h h':M.epoch_hash) =
   (if h'.epoch_complete
    then h == h'
    else (
      h.hadd == zero_hash /\
      h.hevict == zero_hash
   ))

let epoch_id_hash = fun (e:M.epoch_id) -> e
let epoch_hashes_t = IArray.tbl M.epoch_id epoch_hash_t epoch_id_hash
let epoch_hash_contributions_t = Map.t (thread_id & M.epoch_id) M.epoch_hash

let all_contributions_are_accurate (_:IArray.repr M.epoch_id epoch_hash_t)
                                   (_:epoch_hash_contributions_t)
  : prop
  = True //TODO

let max_certified_epoch_is (_:IArray.repr M.epoch_id epoch_hash_t)
                           (_:M.epoch_id)
  : prop
  = True //TODO

let per_thread_contribiution_is_accurate (tid:thread_id)
                                         (entries:Seq.seq log_entry_base)
                                         (contribs:epoch_hash_contributions_t)
  : prop
  = let tsm = M.verify_model (M.init_thread_state_model tid) entries in
    forall (eid:M.epoch_id). related (Map.sel contribs (tid, eid))
                                (Map.sel tsm.epoch_hashes eid)

let full = Steel.FractionalPermission.full_perm
let half = Steel.FractionalPermission.half_perm full
val h_forall (#a:Type u#a) (f: a -> vprop) : vprop

let lock_inv (log_refs:log_refs_t)
             (hashes : epoch_hashes_t)
             (max_certified_epoch : ref M.epoch_id)
             (contributions: ghost_ref epoch_hash_contributions_t)
 : vprop
 = h_exists (fun (hashes_v, max, contributions_v) ->
      IArray.tpts_to hashes hashes_v `star`
      pts_to max_certified_epoch full max `star`
      ghost_pts_to contributions full contributions_v `star`
      pure (all_contributions_are_accurate hashes_v contributions_v /\
            max_certified_epoch_is hashes_v max) `star`
      h_forall (fun (tid:thread_id) ->
        if Map.contains log_refs tid
        then (
          let logref = Map.sel log_refs tid in
          h_exists (fun (entries:_) ->
            ghost_pts_to logref half entries `star`
            pure (per_thread_contribiution_is_accurate tid entries contributions_v))
        )
        else emp
      ))

noeq
type aggregate_epoch_hashes (log_refs:log_refs_t) = {
     hashes : epoch_hashes_t;
     max_certified_epoch : ref M.epoch_id;
     contributions: ghost_ref epoch_hash_contributions_t;
     lock: Lock.lock (lock_inv log_refs hashes max_certified_epoch contributions)
}
