module Zeta.Generic.Global

open FStar.Seq
open Zeta.SeqAux
open Zeta.SSeq
open Zeta.Interleave
open Zeta.Time
open Zeta.MultiSetHashDomain
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

let cond_idxfn #vspec (#b:eqtype) (#f:_) (tfn: cond_idxfn_t #vspec b f)
  (gl: verifiable_log vspec) (ti: sseq_index gl{idxfn f gl ti})
  = let t,i = ti in
    let tl = thread_log gl t in
    tfn tl i

(* a theory of filter-map operations using thread idx functions *)
val filter_map (#vspec:_) (#b:_)
  (fm: fm_t vspec b)
  (gl: verifiable_log vspec)
  : s:sseq b {S.length s = S.length gl}

(* map an index of the original sequence to the filter-mapped sequence *)
val filter_map_map (#vspec:_) (#b:_)
  (fm: fm_t vspec b)
  (gl: verifiable_log vspec)
  (ii: sseq_index gl {idxfn fm.f gl ii})
  : jj: (sseq_index (filter_map fm gl))
    {indexss (filter_map fm gl) jj == cond_idxfn fm.m gl ii /\
     fst ii = fst jj}

(* map an index of the filter-map back to the original sequence *)
val filter_map_invmap (#vspec:_) (#b:_)
  (fm: fm_t vspec b)
  (gl: verifiable_log vspec)
  (jj: sseq_index (filter_map fm gl))
  : ii:(sseq_index gl){idxfn fm.f gl ii /\ filter_map_map fm gl ii = jj }

val lemma_filter_map (#vspec:_)  (#b:_)
  (fm: fm_t vspec b)
  (gl: verifiable_log vspec)
  (ii: sseq_index gl {idxfn fm.f gl ii})
  : Lemma (ensures (let jj = filter_map_map fm gl ii in
                    ii = filter_map_invmap fm gl jj))
          [SMTPat (filter_map_map fm gl ii)]

val lemma_filter_map_idx (#vspec:_) (#b:_)
  (fm: fm_t vspec b)
  (gl: verifiable_log vspec)
  (i: SA.seq_index gl)
  : Lemma (ensures (S.index (filter_map fm gl) i = T.filter_map fm (thread_log gl i)))

let clock #vspec = idxfn (T.clock #vspec)

(* blum add set elements for a given epoch *)
let add_set
  (#vspec: verifier_spec)
  (ep: epoch)
  (gl: verifiable_log vspec): mset_ms_hashfn_dom vspec.app
  = let open Zeta.MultiSet.SSeq in
    (* filter map specification that filter by AddB? and maps them to blum add elem *)
    let fm = to_fm (T.blum_add_elem #vspec #ep) in
    (* get a seq of seq of blum-add-elems and convert them to multiset *)
    sseq2mset (filter_map fm gl)

(* blum evict set elements for a given epoch *)
let evict_set
  (#vspec: verifier_spec)
  (ep: epoch)
  (gl: verifiable_log vspec): mset_ms_hashfn_dom vspec.app
  = let open Zeta.MultiSet.SSeq in
    let fm = to_fm (T.blum_evict_elem #vspec #ep) in
    sseq2mset (filter_map fm gl)

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
  (ep: epoch)
  (gl: verifiable_log vspec): sseq (Zeta.AppSimulate.appfn_call_res vspec.app)
  = let fm = to_fm (T.appfn_call_res #vspec ep) in
    filter_map fm gl
