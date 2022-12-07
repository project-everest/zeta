module Zeta.Steel.GlobalRel

open Zeta.App
open Zeta.AppSimulate
open Zeta.Steel.ApplicationTypes
open Zeta.Steel.ThreadStateModel
open Zeta.Steel.MultiSetHash
open Zeta.Steel.Rel
open Zeta.Steel.ThreadRel
open Zeta.Steel.Thread

module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module GG = Zeta.Generic.Global
module HA = Zeta.Steel.HashAccumulator
module StT = Zeta.Steel.Thread
module AH = Zeta.Steel.AggregateEpochHashes

let index_ (logs: all_logs)  (t: tid)
  : tlog
  = let tv = U16.v t in
    (t, Seq.index logs tv)

let verifiable (logs: all_logs)
  = forall (t: tid). StT.verifiable (index_ logs t)

let verifiable_logs = l: all_logs {verifiable l}

let index (logs: verifiable_logs) (t: tid)
  : StT.verifiable_log
  = index_ logs t

let as_tid_logs (logs:all_logs)
  = Zeta.SeqAux.mapi #_ #(tid & log)
                     logs
                     (fun (i:Zeta.SeqAux.seq_index logs) -> (FStar.UInt16.uint_to_t i, Seq.index logs i))

(* all verifier threads succeed and have certified upto epmax *)
let verifiable_and_certified (logs: all_logs) (epmax: epoch_id)
  = verifiable logs /\
    (forall (eid: epoch_id). (U32.v eid <= U32.v epmax) ==> AH.epoch_is_certified (as_tid_logs logs) eid)

let n_threads_v = U32.v n_threads

let all_app_fcrs (ep: epoch_id) (logs: verifiable_logs)
  : GTot (Seq.seq (Seq.seq (appfn_call_res app)))
  = Seq.init_ghost n_threads_v (fun t -> let tl = index logs (U16.uint_to_t t) in
                               app_fcrs ep tl)

let i_verifiable_logs = Zeta.Intermediate.Global.verifiable_log i_vcfg

val to_ilog (logs: verifiable_logs)
  : GTot (i_logs: i_verifiable_logs {Seq.length i_logs = n_threads_v})

val all_app_fcrs_rel (ep: epoch_id) (logs: verifiable_logs)
  : Lemma (ensures (let s_fcrs = all_app_fcrs ep logs in
                    let i_logs = to_ilog logs in
                    let i_ep = lift_epoch ep in
                    let i_fcrs = GG.app_fcrs_within_ep i_ep i_logs in
                    s_fcrs = i_fcrs))

let hash_value_t = HA.hash_value_t

val aggregate_add_hash (logs: all_logs) (ep: epoch_id)
  : GTot hash_value_t

val aggregate_evict_hash (logs: all_logs) (ep: epoch_id)
  : GTot hash_value_t

val certified_epoch_aggregate_hashes_equal (logs: all_logs) (ep: epoch_id {AH.epoch_is_certified (as_tid_logs logs) ep})
  : Lemma (ensures (aggregate_add_hash logs ep == aggregate_evict_hash logs ep))

val aggr_add_hash_correct (logs: verifiable_logs) (ep: epoch_id)
  : Lemma (requires (AH.epoch_is_certified (as_tid_logs logs) ep))
          (ensures (let gl = to_ilog logs in
                    let i_ep = lift_epoch ep in
                    let add_set = GG.add_set i_ep gl in
                    let h = aggregate_add_hash logs ep in
                    h == ms_hashfn add_set))

val aggr_evict_hash_correct (logs: verifiable_logs) (ep: epoch_id)
  : Lemma (requires (AH.epoch_is_certified (as_tid_logs logs) ep))
          (ensures (let gl = to_ilog logs in
                    let i_ep = lift_epoch ep in
                    let evict_set = GG.evict_set i_ep gl in
                    let h = aggregate_evict_hash logs ep in
                    h == ms_hashfn evict_set))
