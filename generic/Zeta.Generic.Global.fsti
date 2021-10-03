module Zeta.Generic.Global

open FStar.Seq
open Zeta.SeqAux
open Zeta.SSeq
open Zeta.Interleave
open Zeta.MultiSet.SSeq
open Zeta.Time
open Zeta.MultiSetHashDomain
open Zeta.GenericVerifier
open Zeta.Generic.Thread

module S = FStar.Seq
module SS = Zeta.SSeq
module SA = Zeta.SeqAux
module T = Zeta.Generic.Thread
module I = Zeta.Interleave
module GV = Zeta.GenericVerifier

(* a global log is a collection of thread-level verifier logs *)
let vlog (vspec: verifier_spec) = seq (verifier_log vspec)

let thread_log_base #vspec (gl: vlog vspec) (tid: SA.seq_index gl): T.vlog _ =
  (tid, S.index gl tid)

let indexss #vspec (gl: vlog vspec) (i: SS.sseq_index gl) =
  indexss gl i

(* a global log is verifiable if every thread-level log is verifiable *)
let verifiable #vspec (gl: vlog vspec) =
  forall (tid: SA.seq_index gl). {:pattern T.verifiable (thread_log_base gl tid)} T.verifiable (thread_log_base gl tid)

let verifiable_log (vspec: verifier_spec) = gl:vlog vspec {verifiable gl}

val lemma_prefix_verifiable (#vspec:_) (gl: verifiable_log vspec) (l: nat{l <= S.length gl})
  : Lemma (ensures (verifiable (SA.prefix gl l)))
          [SMTPat (SA.prefix gl l)]

let prefix (#vspec:_) (gl: verifiable_log vspec) (l: nat{l <= S.length gl})
  : verifiable_log vspec
  = SA.prefix gl l

let index (#vspec:_) (gl: verifiable_log vspec) (i: SA.seq_index gl)
  : T.verifiable_log vspec
  = thread_log_base gl i

let clock (#vspec:_) (gl: verifiable_log vspec) (i: sseq_index gl)
  : timestamp
  = let tid,j = i in
    let tl = index gl tid in
    T.clock tl j

let epoch_of (#vspec:_) (gl: verifiable_log vspec) (i: sseq_index gl)
  = let tid,j = i in
    let tl = index gl tid in
    T.epoch_of tl j

let is_within_epoch (#vspec:_) (ep: epoch) (gl: verifiable_log vspec) (i: sseq_index gl)
  = epoch_of gl i <= ep

let is_appfn (#vspec:_) (gl: verifiable_log vspec) (i: sseq_index gl)
  : bool
  = let t,j = i in
    let tl = index gl t in
    T.is_appfn tl j

open Zeta.AppSimulate

let to_app_fcr (#vspec:_) (gl: verifiable_log vspec) (i: sseq_index gl{is_appfn gl i})
  : appfn_call_res vspec.app
  = let t,j = i in
    let tl = index gl t in
    T.to_app_fcr tl j

let is_blum_add (#vspec:_) (gl: verifiable_log vspec) (i: sseq_index gl)
  : bool
  = let t,j = i in
    let tl = index gl t in
    T.is_blum_add tl j

let blum_add_elem (#vspec:_) (gl: verifiable_log vspec) (i: sseq_index gl {is_blum_add gl i})
  : ms_hashfn_dom vspec.app
  = let t,j = i in
    let tl = index gl t in
    T.blum_add_elem tl j

let is_blum_evict (#vspec:_)(gl: verifiable_log vspec) (i: sseq_index gl)
  : bool
  = let t,j = i in
    let tl = index gl t in
    T.is_blum_evict tl j

let blum_evict_elem (#vspec:_) (gl: verifiable_log vspec) (i: sseq_index gl {is_blum_evict gl i})
  : ms_hashfn_dom vspec.app
  = let t,j = i in
    let tl = index gl t in
    T.blum_evict_elem tl j

let add_sseq (#vspec:_) (ep: epoch) (gl: verifiable_log vspec)
  : sseq (ms_hashfn_dom vspec.app)
  = S.init (S.length gl) (fun i -> T.add_seq ep (index gl i))

let evict_sseq (#vspec:_) (ep: epoch) (gl: verifiable_log vspec)
  : sseq (ms_hashfn_dom vspec.app)
  = S.init (S.length gl) (fun i -> T.evict_seq ep (index gl i))

(* blum add set elements for a given epoch *)
let add_set
  (#vspec: verifier_spec)
  (ep: epoch)
  (gl: verifiable_log vspec)
  : mset_ms_hashfn_dom vspec.app
  = let as = add_sseq ep gl in
    sseq2mset as

(* blum evict set elements for a given epoch *)
let evict_set
  (#vspec: verifier_spec)
  (ep: epoch)
  (gl: verifiable_log vspec): mset_ms_hashfn_dom vspec.app
  = let es = evict_sseq ep gl in
    sseq2mset es

(* verifiable log property that add- and evict sets are the same *)
let aems_equal_for_epoch #vspec
  (ep: epoch)
  (gl: verifiable_log vspec) =
  add_set ep gl == evict_set ep gl

(* add and evict sets are equal for all epochs upto epmax *)
let aems_equal_upto #vspec (epmax: epoch) (gl: verifiable_log vspec) =
  forall (ep: epoch).
  ep <= epmax ==> add_set ep gl == evict_set ep gl

(* global log whose add and evict multisets are equal *)
let ms_verifiable_log #vspec (ep: epoch)
  = gl:verifiable_log vspec{aems_equal_upto ep gl}

(* filter-mapped sequence of sequence app-function-call results *)
let app_fcrs
  (#vspec: verifier_spec)
  (gl: verifiable_log vspec): sseq (Zeta.AppSimulate.appfn_call_res vspec.app)
  = S.init (S.length gl) (fun i -> T.app_fcrs (index gl i))

let app_fcrs_within_ep
  (#vspec: verifier_spec)
  (ep: epoch)
  (gl: verifiable_log vspec): sseq (Zeta.AppSimulate.appfn_call_res vspec.app)
  = S.init (S.length gl) (fun i -> T.app_fcrs_within_ep ep (index gl i))
