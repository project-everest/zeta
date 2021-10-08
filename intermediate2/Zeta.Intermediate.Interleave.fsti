module Zeta.Intermediate.Interleave

open FStar.Seq
open Zeta.Interleave
open Zeta.Intermediate.VerifierConfig
open Zeta.Intermediate.Verifier
open Zeta.Generic.Interleave

let ilog (vcfg: verifier_config) =
  Zeta.Generic.Interleave.ilog (int_verifier_spec vcfg) (vcfg.thread_count)

let verifiable_log (vcfg: verifier_config)
  = il: ilog vcfg {verifiable il}

let thread_store (#vcfg:_) (tid:nat{tid < vcfg.thread_count}) (il: verifiable_log vcfg)
  = let vs = thread_state tid il in
    vs.st

let thread_store_pre (#vcfg:_) (tid: nat{tid < vcfg.thread_count}) (il: verifiable_log vcfg) (i: seq_index il)
  = let vs = thread_state_pre tid il i in
    vs.st

let thread_store_post (#vcfg:_) (tid: nat{tid < vcfg.thread_count}) (il: verifiable_log vcfg) (i: seq_index il)
  = let vs = thread_state_post tid il i in
    vs.st
