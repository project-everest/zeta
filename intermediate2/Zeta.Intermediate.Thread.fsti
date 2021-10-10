module Zeta.Intermediate.Thread

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

val to_logk_entry (#vcfg:_) (tl: verifiable_log vcfg) (i: seq_index tl)
  : logK_entry vcfg.app
