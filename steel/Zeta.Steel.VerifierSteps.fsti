module Zeta.Steel.VerifierSteps
include Zeta.Steel.VerifierTypes
open FStar.Ghost
open Steel.ST.Util
open Zeta.Steel.ApplicationTypes
open Zeta.Steel.FormatsManual
open Zeta.Steel.Util
module M = Zeta.Steel.ThreadStateModel
module T = Zeta.Steel.FormatsManual
#push-options "--ide_id_info_off"

val create (tid:tid)
  : STT thread_state_t
    emp
    (fun t -> thread_state_inv t (M.init_thread_state_model tid))

val vaddm (#tsm:M.thread_state_model)
          (t:thread_state_t)
          (s s':slot_id)
          (r:T.record)
  : STT bool
    (thread_state_inv_core t tsm)
    (fun b ->
      thread_state_inv_core t
           (update_if b tsm (M.vaddm tsm s s' r)))

val vaddb (#tsm:M.thread_state_model)
          (t:thread_state_t)
          (s:slot_id)
          (ts:timestamp)
          (thread_id:T.thread_id)
          (r:T.record)
  : STT bool
       (thread_state_inv_core t tsm)
       (fun b ->
         thread_state_inv_core t
               (update_if b tsm (M.vaddb tsm s ts thread_id r)))

val vevictm (#tsm:M.thread_state_model)
            (t:thread_state_t)
            (s s':slot_id)
  : STT unit
    (thread_state_inv_core t tsm)
    (fun _ -> thread_state_inv_core t (M.vevictm tsm s s'))

val vevictb (#tsm:M.thread_state_model)
            (t:thread_state_t)
            (s:slot_id)
            (ts:timestamp)
  : ST bool
    (thread_state_inv_core t tsm)
    (fun b -> thread_state_inv_core t (update_if b tsm (M.vevictb tsm s ts)))
    (requires VerifierTypes.thread_id t == tsm.thread_id)
    (ensures fun _ -> True)

val vevictbm (#tsm:M.thread_state_model)
             (t:thread_state_t)
             (s s':slot_id)
             (ts:timestamp)
  : ST bool
    (thread_state_inv_core t tsm)
    (fun b -> thread_state_inv_core t (update_if b tsm (M.vevictbm tsm s s' ts)))
    (VerifierTypes.thread_id t == tsm.thread_id)
    (fun _ -> True)

val nextepoch (#tsm:M.thread_state_model)
              (t:thread_state_t)
  : STT unit
    (thread_state_inv_core t tsm)
    (fun _ -> thread_state_inv_core t (M.nextepoch tsm))

module AEH = Zeta.Steel.AggregateEpochHashes
module TLM = Zeta.Steel.ThreadLogMap
let spec_verify_epoch (tsm:M.thread_state_model)
  = let tsm = M.verifyepoch tsm in
    if tsm.failed then tsm
    else { tsm with M.processed_entries = Seq.snoc tsm.processed_entries (VerifyEpoch)}

val verify_epoch (#tsm:M.thread_state_model)
                 (t:thread_state_t)
                 (aeh:AEH.aggregate_epoch_hashes)
  : ST bool
    (thread_state_inv t tsm `star`
     TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false)
    (fun b ->
      thread_state_inv t (update_if b tsm (spec_verify_epoch tsm)) `star`
      TLM.tid_pts_to aeh.mlogs tsm.thread_id full (update_if b tsm.processed_entries
                                                         (spec_verify_epoch tsm).processed_entries)
                                            false)
    (requires not tsm.failed)
    (ensures fun _ -> True)
