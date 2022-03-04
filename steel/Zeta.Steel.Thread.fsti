module Zeta.Steel.Thread

open Zeta.AppSimulate
open Zeta.Steel.Rel
open Zeta.Steel.ThreadStateModel
open Zeta.Steel.ThreadRelDef
open Zeta.Steel.ThreadRel

module AT = Zeta.Steel.ApplicationTypes
module GT = Zeta.Generic.Thread
module T = Zeta.Steel.FormatsManual
module TSM = Zeta.Steel.ThreadStateModel


let tlog = AT.tid & log

let length (tl: tlog)
  = let t,l = tl in
    Seq.length l

let seq_index tl = i:nat {i < length tl}

let index tl (i: seq_index tl)
  = let t,l = tl in
    Seq.index l i

let verifiable (tl: tlog)
  = let t,l = tl in
    let tsm = run t l in
    not tsm.failed

let verifiable_log = tl: tlog {verifiable tl}

val to_tsm (tl: verifiable_log)
  : tsm:valid_tsm {let t,l = tl in
                   tsm.processed_entries == l /\
                   tsm.thread_id == t}

(* set of app function calls and results that happen within epoch ep *)
val app_fcrs (ep: TSM.epoch_id) (tl: verifiable_log)
  : GTot (Seq.seq (appfn_call_res app))

val spec_rel_implies_same_fcrs (ep: TSM.epoch_id) (tl: verifiable_log)
  : Lemma (ensures (let s_fcrs = app_fcrs ep tl in
                    let tsm = to_tsm tl in
                    let tl = to_ilog tsm in
                    let i_ep = lift_epoch ep in
                    let i_fcrs = GT.app_fcrs_within_ep i_ep tl in
                    s_fcrs == i_fcrs))
