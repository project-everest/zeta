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

let clock_sorted (#vspec:_) (il: verifiable_log vspec) =
  forall (i j: I.seq_index il). i <= j ==> clock il i `ts_leq` clock il j

let its_log vspec = il:verifiable_log vspec{clock_sorted il}

val lemma_prefix_clock_sorted (#vspec:_) (itsl: its_log vspec) (i:nat{i <= I.length itsl}):
  Lemma (ensures (clock_sorted (prefix itsl i)))
        [SMTPat (I.prefix itsl i)]

val create (#vspec:_) (gl: G.verifiable_log vspec): (itsl:its_log vspec{to_glog itsl == gl})
