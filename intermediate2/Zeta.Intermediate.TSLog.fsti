module Zeta.Intermediate.TSLog

open Zeta.Generic.TSLog
open Zeta.Intermediate.VerifierConfig
open Zeta.Intermediate.Verifier
open Zeta.Intermediate.Interleave

module T = Zeta.Generic.TSLog

let its_log (vcfg:_)
  = T.its_log (int_verifier_spec vcfg) (vcfg.thread_count)
