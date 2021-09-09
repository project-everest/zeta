module Zeta.Generic.Global

open FStar.Seq
open Zeta.SeqAux
open Zeta.SSeq
open Zeta.IdxFn
open Zeta.SIdxFn
open Zeta.Interleave
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

let verifiable_log vspec = gl:vlog vspec {verifiable gl}

val lemma_prefix_verifiable (#vspec:_) (gl: verifiable_log vspec) (l: nat{l <= S.length gl})
  : Lemma (ensures (verifiable (SA.prefix gl l)))
          [SMTPat (SA.prefix gl l)]

let prefix (#vspec:_) (gl: verifiable_log vspec) (l: nat{l <= S.length gl})
  : gl':verifiable_log vspec {S.length gl' = l}
  = SA.prefix gl l

let index (#vspec:_) (gl: verifiable_log vspec) (i: SA.seq_index gl)
  : T.verifiable_log vspec
  = thread_log_base gl i

let gso (vspec: verifier_spec) : gen_seq_spec = {
  seq_t = verifiable_log vspec;
  length = S.length;
  prefix
}

let gen_sseq (vspec:verifier_spec): gen_sseq = {
  gso = gso vspec;
  gsi = T.gen_seq vspec;
  index
}

let idxfn (#vspec:verifier_spec) #b (f: T.idxfn_t vspec b) (gl: verifiable_log vspec) (ii: sseq_index gl)
  = Zeta.SIdxFn.idxfn #b (gen_sseq vspec) f gl ii

let cond_idxfn (#b:_) (#vspec:verifier_spec) (#f: T.idxfn_t vspec bool)
  = Zeta.SIdxFn.cond_idxfn #b #(gen_sseq vspec) #f

let clock #vspec = idxfn (T.clock #vspec)

(* blum add set elements for a given epoch *)
let add_set
  (#vspec: verifier_spec)
  (ep: epoch)
  (gl: verifiable_log vspec): mset_ms_hashfn_dom vspec.app
  = let open Zeta.MultiSet.SSeq in
    (* filter map specification that filter by AddB? and maps them to blum add elem *)
    let fm = to_fm (T.is_blum_add_ep ep) (T.blum_add_elem #vspec) in
    (* get a seq of seq of blum-add-elems and convert them to multiset *)
    sseq2mset (filter_map (gen_sseq vspec) fm gl)

(* blum evict set elements for a given epoch *)
let evict_set
  (#vspec: verifier_spec)
  (ep: epoch)
  (gl: verifiable_log vspec): mset_ms_hashfn_dom vspec.app
  = let open Zeta.MultiSet.SSeq in
    let fm = to_fm (T.is_blum_evict_ep ep) (T.blum_evict_elem #vspec) in
    sseq2mset (filter_map (gen_sseq vspec) fm gl)

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
let appfn_calls
  (#vspec: verifier_spec)
  (gl: verifiable_log vspec): sseq (Zeta.AppSimulate.appfn_call_res vspec.app)
  = let fm = to_fm (T.is_appfn #vspec) (T.to_appfn_call_res #vspec) in
    filter_map (gen_sseq vspec) fm gl

let appfn_calls_within_ep
  (#vspec: verifier_spec)
  (ep: epoch)
  (gl: verifiable_log vspec): sseq (Zeta.AppSimulate.appfn_call_res vspec.app)
  = let fm = to_fm (T.is_appfn_within_epoch #vspec ep) (T.to_appfn_call_res #vspec) in
    filter_map (gen_sseq vspec) fm gl
