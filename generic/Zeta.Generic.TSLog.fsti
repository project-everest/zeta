module Zeta.Generic.TSLog

open FStar.Seq
open Zeta.SeqAux
open Zeta.Interleave
open Zeta.Time
open Zeta.GenericVerifier
open Zeta.Generic.Thread
open Zeta.Generic.Global

module V = Zeta.GenericVerifier
module T = Zeta.Generic.Thread
module G = Zeta.Generic.Global
module I = Zeta.Interleave

let ilog (vspec: verifier_spec) = interleaving (verifier_log_entry vspec)

(* valid thread ids of an interleaving *)
let thread_id #vspec (il: ilog vspec) = Zeta.Thread.thread_id

(* to sequence of individual thread-level logs *)
let to_gvlog #vspec (il: ilog vspec): G.vlog _
  = I.s_seq il

(* an interleaving is verifiable is the source logs are verifiable *)
let verifiable #vspec (il: ilog vspec) =
  G.verifiable (to_gvlog il)

let seq_index #vspec (il: ilog vspec) = I.seq_index il

let prefix #vspec (il: ilog vspec) = I.prefix il

let clock #vspec (il: ilog vspec {verifiable il}) (i: seq_index il) =
  let j = i2s_map il i in
  G.clock (to_gvlog il) j

let clock_sorted (#vspec:_) (il: ilog vspec {verifiable il}) =
  forall (i j: I.seq_index il). i <= j ==> clock il i `ts_leq` clock il j

let its_log vspec = il:ilog vspec{verifiable il /\ clock_sorted il}

val lemma_prefix_verifiable (#vspec:_) (itsl: its_log vspec) (i:nat{i <= I.length itsl}):
  Lemma (ensures (verifiable (I.prefix itsl i) /\ clock_sorted (I.prefix itsl i)))
        [SMTPat (I.prefix itsl i)]

val create (#vspec:_) (gl: verifiable_log vspec): (itsl:its_log vspec{to_gvlog itsl == gl})
