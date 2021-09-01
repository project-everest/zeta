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

let idxfn #vspec (#b:eqtype) (tfn: idxfn_t vspec b) (gl: verifiable_log vspec) (ti: sseq_index gl): b
  = let t,i = ti in
    let tl = thread_log gl t in
    tfn tl i

let clock #vspec = idxfn (T.clock #vspec)

(* given a conditional thread index function (e.g., blum_evict_elem) we can construct a filter-map pred *)
val to_fm (#vspec: verifier_spec) (#b:eqtype) (#pred:_) (p:nat) (tfn: cond_idxfn_t #vspec b pred)
  : ssfm_t (verifier_log_entry vspec) b p

(* blum add set elements for a given epoch *)
let add_set
  (#vspec: verifier_spec)
  (ep: epoch)
  (gl: verifiable_log vspec): mset_ms_hashfn_dom vspec.app
  = let open Zeta.MultiSet.SSeq in
    (* filter map specification that filter by AddB? and maps them to blum add elem *)
    let fm = to_fm (S.length gl) (T.blum_add_elem #vspec #ep) in
    (* get a seq of seq of blum-add-elems and convert them to multiset *)
    sseq2mset (ssfilter_map fm gl)

(* blum evict set elements for a given epoch *)
let evict_set
  (#vspec: verifier_spec)
  (ep: epoch)
  (gl: verifiable_log vspec): mset_ms_hashfn_dom vspec.app
  = let open Zeta.MultiSet.SSeq in
    let fm = to_fm (S.length gl) (T.blum_evict_elem #vspec #ep) in
    sseq2mset (ssfilter_map fm gl)

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

(* filter-mapped sequence of sequence app-function-call results *)
let appfn_call_res
  (#vspec: verifier_spec)
  (gl: verifiable_log vspec): sseq (Zeta.AppSimulate.appfn_call_res vspec.app)
  = let fm = to_fm (S.length gl) (T.appfn_call_res #vspec) in
    ssfilter_map fm gl
