module Zeta.Generic.Global

open FStar.Seq
open Zeta.SeqAux
open Zeta.SSeq
open Zeta.Interleave
open Zeta.Time
open Zeta.MultiSetHashDomain
open Zeta.FilterMap
open Zeta.GenericVerifier
open Zeta.Generic.Thread

module S = FStar.Seq
module SA = Zeta.SeqAux
module T = Zeta.Generic.Thread
module I = Zeta.Interleave
module GV = Zeta.GenericVerifier

(* a global log is a collection of thread-level verifier logs *)
let vlog (vspec: verifier_spec) = seq (verifier_log vspec)

let thread_log #vspec (gl: vlog vspec) (tid: SA.seq_index gl): T.vlog _ =
  (tid, S.index gl tid)

let index #vspec (gl: vlog vspec) (i: sseq_index gl) =
  indexss gl i

(* a global log is verifiable if every thread-level log is verifiable *)
let verifiable #vspec (gl: vlog vspec) =
  forall (tid: SA.seq_index gl). {:pattern T.verifiable (thread_log gl tid)} T.verifiable (thread_log gl tid)

let verifiable_log vspec = gl:vlog vspec {verifiable gl}

let clock #vspec (gl: verifiable_log vspec) (i: sseq_index gl) =
  let tid, i' = i in
  let tl = thread_log gl tid in
  T.clock tl i'


(* blum add set elements for a given epoch *)
let add_set
  (#vspec: verifier_spec)
  (ep: epoch)
  (gl: verifiable_log vspec): mset_ms_hashfn_dom vspec.app
  = admit()

(* blum evict set elements for a given epoch *)
val evict_set
  (#vspec: verifier_spec)
  (ep: epoch)
  (gl: verifiable_log vspec): mset_ms_hashfn_dom vspec.app

(* verifiable log property that add- and evict sets are the same *)
let aems_equal_for_epoch #vspec
  (ep: epoch)
  (gl: verifiable_log vspec) =
  add_set ep gl == evict_set ep gl

let aems_equal_for_epoch_prop #vspec
  (ep: epoch)
  (gl: verifiable_log vspec)
  (epmax: epoch) =
  ep <= epmax ==> aems_equal_for_epoch ep gl

(* add and evict sets are equal for all epochs upto epmax *)
let aems_equal_upto #vspec (epmax: epoch) (gl: verifiable_log vspec) =
  forall (ep: epoch).
  {:pattern aems_equal_for_epoch_prop ep gl epmax}
  aems_equal_for_epoch_prop ep gl epmax

(* global log whose add and evict multisets are equal *)
let ms_verifiable_log #vspec (ep: epoch)
  = gl:verifiable_log vspec{aems_equal_upto ep gl}
