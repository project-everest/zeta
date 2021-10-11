module Zeta.Intermediate.TSLog

open FStar.Seq
open Zeta.Interleave
open Zeta.Generic.Interleave
open Zeta.Generic.TSLog
open Zeta.Intermediate.VerifierConfig
open Zeta.Intermediate.Verifier
open Zeta.Intermediate.Interleave

module T = Zeta.Generic.TSLog
module I = Zeta.Interleave
module HT = Zeta.High.TSLog

let its_log (vcfg:_)
  = T.its_log (int_verifier_spec vcfg) (vcfg.thread_count)

val lemma_vtls_rel_implies_spec_clock_sorted (#vcfg:_) (ils:its_log vcfg)
  : Lemma (requires (forall_vtls_rel ils))
          (ensures (let ilk = to_logk ils  in
                    T.clock_sorted ilk))
          [SMTPat (forall_vtls_rel ils)]
