module Zeta.Steel.ThreadRel

(* This module sets up the relationship between a steel verifier thread and a spec-level one *)

open Zeta.App
open Zeta.AppSimulate
open Zeta.Steel.KeyUtils
open Zeta.Steel.Rel
open Zeta.Steel.LogRel
open Zeta.Steel.StoreRel
open Zeta.Steel.MultiSetHash
open Zeta.Steel.ThreadStateModel
open Zeta.Steel.ThreadRelDef

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module L = FStar.List.Tot
module GK = Zeta.GenKey
module K = Zeta.Key
module M = Zeta.Merkle
module GV = Zeta.GenericVerifier
module GT = Zeta.Generic.Thread
module IL = Zeta.Intermediate.Logs
module IV = Zeta.Intermediate.Verifier
module AT = Zeta.Steel.ApplicationTypes
module T = Zeta.Steel.FormatsManual
module TSM = Zeta.Steel.ThreadStateModel
module MS = Zeta.MultiSet

(* thread_state_model has some redundancy - for tsm's of interest, the state is obtained by
 * running the log from an initial state. *)
let valid (tsm: thread_state_model)
  = U16.v tsm.thread_id < U32.v AT.n_threads /\
    tsm == run tsm.thread_id tsm.processed_entries /\
    not tsm.failed

(* this type captures the class of well-behaved tsms we are interested in *)
let valid_tsm = tsm: thread_state_model { valid tsm }

(* the processed_entries of a valid tsm is a valid log - otherwise, the verify_step should have failed ... *)
val valid_implies_valid_log (tsm: valid_tsm)
  : Lemma (ensures (valid_log tsm.processed_entries))
          [SMTPat (valid_log tsm.processed_entries)]


let related_tsm_valid (s: s_thread_state) (i: i_thread_state)
  = related_tsm s i /\
    not s.failed

(* tsm and its lifted spec version are related in all fields except epoch_hashes .... *)
let spec_rel_base (tsm: valid_tsm)
  = let open Zeta.Generic.Thread in
    let open IV in
    let open TSM in
    let i_log = lift_log tsm.processed_entries in
    let i_tid = lift_tid tsm.thread_id in
    let i_tl = (i_tid, i_log) in
    let i_tsm = state i_tl in

    related_tsm tsm i_tsm

let i_verifiable_log = Zeta.Intermediate.Thread.verifiable_log i_vcfg

let to_ilog (tsm: valid_tsm {spec_rel_base tsm})
  : GTot i_verifiable_log
  = let i_log = lift_log tsm.processed_entries in
    let i_tid = lift_tid tsm.thread_id in
    (i_tid, i_log)

let add_set (tsm: valid_tsm {spec_rel_base tsm}) (ep: i_epoch)
  : GTot mset
  = let tl = to_ilog tsm in
    let add_seq = Zeta.Generic.Thread.add_seq ep tl in
    MS.seq2mset add_seq

let evict_set (tsm: valid_tsm {spec_rel_base tsm}) (ep: i_epoch)
  : GTot mset
  = let tl = to_ilog tsm in
    let evict_seq = Zeta.Generic.Thread.evict_seq ep tl in
    MS.seq2mset evict_seq

(* spec_rel_base plus the epoch hashes are related to the add/evict sets *)
let spec_rel (tsm: valid_tsm)
  = spec_rel_base tsm /\
    (forall (s_ep: epoch_id). let i_ep = lift_epoch s_ep in
                          let eh = Map.sel tsm.epoch_hashes s_ep in
                          eh.hadd = ms_hashfn (add_set tsm i_ep) /\
                          eh.hevict = ms_hashfn (evict_set tsm i_ep))

val valid_implies_spec_rel (tsm: valid_tsm)
  : Lemma (ensures (spec_rel tsm))
          [SMTPat (valid tsm)]

val valid_hadd_prop (ep: TSM.epoch_id) (tsm: valid_tsm)
  : Lemma (ensures (let i_ep = lift_epoch ep in
                    let eh = Map.sel tsm.epoch_hashes ep in
                    eh.hadd = ms_hashfn (add_set tsm i_ep)))

val valid_hevict_prop (ep: TSM.epoch_id) (tsm: valid_tsm)
  : Lemma (ensures (let i_ep = lift_epoch ep in
                    let eh = Map.sel tsm.epoch_hashes ep in
                    eh.hevict = ms_hashfn (evict_set tsm i_ep)))

val run_props (tid: AT.tid) (l: s_log)
  : Lemma (ensures (let tsm = run tid l in
                    (not tsm.failed) ==> (valid tsm /\
                                         tsm.thread_id = tid /\
                                         tsm.processed_entries == l)))
