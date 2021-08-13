module Zeta.Generic.Global

open FStar.Seq
open Zeta.SeqAux
open Zeta.Interleave
open Zeta.Time
open Zeta.GenericVerifier
open Zeta.Generic.Thread

module S = FStar.Seq
module SA = Zeta.SeqAux
module T = Zeta.Generic.Thread
module I = Zeta.Interleave

(* a global log is a collection of thread-level verifier logs *)
let vlog (vspec: verifier_spec) = seq (verifier_log vspec)

let thread_log #vspec (gl: vlog vspec) (tid: SA.seq_index gl): T.vlog _ =
  (tid, S.index gl tid)

let index #vspec (gl: vlog vspec) (i: sseq_index gl) =
  I.indexss gl i

(* a global log is verifiable if every thread-level log is verifiable *)
let verifiable #vspec (gl: vlog vspec) =
  forall (tid: SA.seq_index gl). {:pattern T.verifiable (thread_log gl tid)} T.verifiable (thread_log gl tid)

let verifiable_log vspec = gl:vlog vspec {verifiable gl}

let clock #vspec (gl: verifiable_log vspec) (i: sseq_index gl) =
  let tid, i' = i in
  let tl = thread_log gl tid in
  T.clock tl i'
