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
module T = Zeta.Generic.Thread
module S = FStar.Seq
module SA = Zeta.SeqAux

let clock_sorted (#vspec:_) (#n:_) (il: verifiable_log vspec n) =
  forall (i j: seq_index il). i <= j ==> clock il i `ts_leq` clock il j

let its_log vspec n = il:verifiable_log vspec n{clock_sorted il}

val lemma_prefix_clock_sorted (#vspec #n:_) (itsl: its_log vspec n) (i:nat{i <= length itsl}):
  Lemma (ensures (clock_sorted (prefix itsl i)))
        [SMTPat (prefix itsl i)]

val create (#vspec:_) (gl: G.verifiable_log vspec): (itsl:its_log vspec (S.length gl){to_glog itsl == gl})

val prefix_within_epoch (#vspec #n:_) (ep: epoch) (itsl: its_log vspec n)
  : itsl': its_log vspec n {itsl' `prefix_of` itsl}

val prefix_within_epoch_correct (#vspec #n:_) (ep: epoch) (itsl: its_log vspec n) (i: seq_index itsl)
  : Lemma (ensures (let il' = prefix_within_epoch ep itsl in
                    let l' = S.length il' in
                    (i < l' ==> (clock itsl i).e <= ep) /\
                    (i >= l' ==> (clock itsl i).e > ep)))

val lemma_appfn_calls_within_epoch (#vspec #n:_) (ep: epoch) (itsl: its_log vspec n)
  : Lemma (ensures (let itsl_ep = prefix_within_epoch ep itsl in
                    let gl_ep = to_glog itsl_ep in
                    let gl = to_glog itsl in
                    G.appfn_calls gl_ep = G.appfn_calls_within_ep ep gl))
