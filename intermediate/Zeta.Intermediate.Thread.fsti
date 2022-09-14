module Zeta.Intermediate.Thread

open Zeta.Intermediate.Store
open Zeta.Intermediate.Verifier
open Zeta.Intermediate.Logs
open Zeta.Intermediate.StateRel
open Zeta.Generic.Thread

module HT = Zeta.High.Thread

let verifiable_log (vcfg:_)
  = Zeta.Generic.Thread.verifiable_log (int_verifier_spec vcfg)

let store (#vcfg:_) (tl: verifiable_log vcfg)
  = let vs = state tl in
    vs.st

let store_pre (#vcfg:_) (tl: verifiable_log vcfg) (i: seq_index tl)
  = let tl' = prefix tl i in
    store tl'

let store_post (#vcfg:_) (tl: verifiable_log vcfg) (i: seq_index tl)
  = let tl' = prefix tl (i+1) in
    store tl'

val verifiable_implies_valid_log_entry
  (#vcfg:_)
  (tl: verifiable_log vcfg)
  (i: seq_index tl)
  : Lemma (ensures (let st = store_pre tl i in
                    let e = index tl i in
                    let s2k = Store.to_slot_state_map st in
                    Logs.valid_logS_entry s2k e))
          [SMTPat (index tl i)]

let to_logk_entry (#vcfg:_) (tl: verifiable_log vcfg) (i: seq_index tl)
  : GTot (logK_entry vcfg.app)
  = let st = store_pre tl i in
    let s2k = Store.to_slot_state_map st in
    let e = index tl i in
    Logs.to_logk_entry s2k e

val lemma_slot_is_merkle_points_to (#vcfg:_) (tl: verifiable_log vcfg)
  : Lemma (ensures (let st = store tl in
                    slot_points_to_is_merkle_points_to st))
          [SMTPat (store tl)]

val empty_log_is_map (#vcfg:_) (tl: verifiable_log vcfg)
  : Lemma (ensures (length tl = 0 ==> is_map (store tl)))

let thread_rel (#vcfg:_) (tls: verifiable_log vcfg) (tlk: HT.verifiable_log vcfg.app)
  = let vts = state tls in
    let vtk = state tlk in
    vtls_rel vts vtk /\
    length tls = length tlk /\
    (forall i. vtls_rel (state_pre tls i) (state_pre tlk i)) /\
    (forall i. (index tlk i) = to_logk_entry tls i)

val thread_rel_implies_fcrs_identical (#vcfg:_) (tls: verifiable_log vcfg) (tlk:_ {thread_rel tls tlk})
  : Lemma (ensures (app_fcrs tls == app_fcrs tlk))
