module Zeta.Generic.TSLog

open FStar.Seq
open Zeta.SeqAux
open Zeta.Interleave
open Zeta.Time
open Zeta.GenericVerifier
open Zeta.Generic.Thread
open Zeta.Generic.Global
open Zeta.Generic.Interleave

module I = Zeta.Interleave
module G = Zeta.Generic.Global
module S = FStar.Seq
module SA = Zeta.SeqAux

let clock_sorted (#vspec:_) (#n:_) (il: verifiable_log vspec n) =
  forall (i j: seq_index il). i <= j ==> clock il i `ts_leq` clock il j

let its_log vspec n = il:verifiable_log vspec n{clock_sorted il}

val lemma_prefix_clock_sorted (#vspec #n:_) (itsl: its_log vspec n) (i:nat{i <= length itsl}):
  Lemma (ensures (clock_sorted (prefix itsl i)))
        [SMTPat (prefix itsl i)]

val create (#vspec:_) (gl: G.verifiable_log vspec): (itsl:its_log vspec (S.length gl){to_glog itsl == gl})
