module Zeta.Steel.VerifierSteps
include Zeta.Steel.VerifierTypes
open FStar.Ghost
open Steel.ST.Util
open Zeta.Steel.ApplicationTypes
open Zeta.Steel.FormatsManual
open Zeta.Steel.Util
module M = Zeta.Steel.ThreadStateModel
module T = Zeta.Steel.FormatsManual
module AEH = Zeta.Steel.AggregateEpochHashes
module TLM = Zeta.Steel.ThreadLogMap
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
    (thread_state_inv t tsm)
    (fun b ->
      thread_state_inv t
           (update_if b tsm (M.verify_step_model tsm (AddM s s' r))))

val vaddb (#tsm:M.thread_state_model)
          (t:thread_state_t)
          (s:slot_id)
          (ts:timestamp)
          (thread_id:T.thread_id)
          (r:T.record)
  : STT bool
       (thread_state_inv t tsm)
       (fun b ->
         thread_state_inv t
               (update_if b tsm (M.verify_step_model tsm (AddB s ts thread_id r))))

val vevictm (#tsm:M.thread_state_model)
            (t:thread_state_t)
            (s s':slot_id)
  : STT unit
    (thread_state_inv t tsm)
    (fun _ -> thread_state_inv t (M.verify_step_model tsm (EvictM ({s; s'}))))

val vevictb (#tsm:M.thread_state_model)
            (t:thread_state_t)
            (s:slot_id)
            (ts:timestamp)
  : STT bool
    (thread_state_inv t tsm)
    (fun b -> thread_state_inv t (update_if b tsm (M.verify_step_model tsm (EvictB ({s; t=ts})))))

val vevictbm (#tsm:M.thread_state_model)
             (t:thread_state_t)
             (s s':slot_id)
             (ts:timestamp)
  : STT bool
    (thread_state_inv t tsm)
    (fun b -> thread_state_inv t (update_if b tsm (M.verify_step_model tsm (EvictBM ({s; s'; t=ts})))))

val nextepoch (#tsm:M.thread_state_model)
              (t:thread_state_t)
  : STT unit
    (thread_state_inv t tsm)
    (fun _ -> thread_state_inv t (M.verify_step_model tsm NextEpoch))

val verify_epoch (#tsm:M.thread_state_model)
                 (t:thread_state_t)
                 (aeh:AEH.aggregate_epoch_hashes)
  : ST bool
    (thread_state_inv t tsm `star`
     TLM.tid_pts_to aeh.mlogs tsm.thread_id full tsm.processed_entries false)
    (fun b ->
      thread_state_inv t (update_if b tsm (M.verify_step_model tsm VerifyEpoch)) `star`
      TLM.tid_pts_to aeh.mlogs tsm.thread_id full (update_if b tsm.processed_entries
                                                         (M.verify_step_model tsm VerifyEpoch).processed_entries)
                                            false)
    (requires not tsm.failed)
    (ensures fun _ -> True)
