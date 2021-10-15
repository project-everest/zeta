module Zeta.Intermediate.Thread

open Zeta.Intermediate.Store
open Zeta.Intermediate.Verifier
open Zeta.Intermediate.Logs
open Zeta.Generic.Thread

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
                    valid_logS_entry s2k e))
          [SMTPat (index tl i)]

let to_logk_entry (#vcfg:_) (tl: verifiable_log vcfg) (i: seq_index tl)
  : logK_entry vcfg.app
  = let st = store_pre tl i in
    let s2k = Store.to_slot_state_map st in
    let e = index tl i in
    Logs.to_logk_entry s2k e

val lemma_slot_is_merkle_points_to (#vcfg:_) (tl: verifiable_log vcfg)
  : Lemma (ensures (let st = store tl in
                    slot_points_to_is_merkle_points_to st))
          [SMTPat (store tl)]
