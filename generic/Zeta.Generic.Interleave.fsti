module Zeta.Generic.Interleave

open FStar.Seq
open Zeta.SeqAux
open Zeta.Time
open Zeta.GenericVerifier
open Zeta.Generic.Thread
open Zeta.Generic.Global
open Zeta.Interleave
module V = Zeta.GenericVerifier
module T = Zeta.Generic.Thread
module G = Zeta.Generic.Global
module I = Zeta.Interleave

let ilog (vspec: verifier_spec) = interleaving (verifier_log_entry vspec)

(* valid thread ids of an interleaving *)
let thread_id #vspec (il: ilog vspec) = Zeta.Thread.thread_id

(* to sequence of individual thread-level logs *)
let to_glog #vspec (il: ilog vspec): G.vlog _
  = I.s_seq il

let seq_index #vspec (il: ilog vspec) = I.seq_index il

let prefix #vspec (il: ilog vspec) = I.prefix il

(* an interleaving is verifiable is the source logs are verifiable *)
let verifiable #vspec (il: ilog vspec) =
  G.verifiable (to_glog il)

let verifiable_log vspec = il:ilog vspec {verifiable il}

val lemma_prefix_verifiable (#vspec:_) (il:verifiable_log vspec) (i:nat{i <= I.length il}):
  Lemma (ensures (verifiable (prefix il i)))
        [SMTPat (prefix il i)]

(* an index function defined over positions of an interleaving *)
let idxfn_t_base vspec (b:eqtype) = il:verifiable_log vspec -> i:seq_index il -> b

let prefix_property
  (#vspec:_)
  (#b:eqtype)
  (f: idxfn_t_base vspec b)
  = forall (il: verifiable_log vspec) (i: nat) (j: nat).
    {:pattern f (prefix il j) i}
    j <= length il ==>
    i < j ==>
    f il i = f (prefix il j) i

let idxfn_t vspec (b: eqtype) = f: idxfn_t_base vspec b {prefix_property f}

let cond_idxfn_t_base (#vspec:_) (b:eqtype) (f:idxfn_t vspec bool)
  = il:verifiable_log vspec -> i:seq_index il{f il i} -> b

let cond_prefix_property
  (#vspec:_)
  (#b:_)
  (#f:_)
  (m: cond_idxfn_t_base b f)
  = forall (il: verifiable_log vspec) (i: nat) (j: nat).
    {:pattern m (prefix il j) i}
    j <= length il ==>
    i < j ==>
    f il i ==>
    m il i = m (prefix il j) i

let cond_idxfn_t (#vspec:_) (b:eqtype) (f:idxfn_t vspec bool)
  = m:cond_idxfn_t_base b f{cond_prefix_property m}

(* a specification of a filter-map *)
noeq
type fm_t (vspec:_) (b:eqtype) =
  | FM: f: _   ->
        m: cond_idxfn_t #vspec b f -> fm_t vspec b

val filter_map (#vspec:_) (#b:eqtype)
  (fm: fm_t vspec b)
  (il: verifiable_log vspec)
  : interleaving b

val filter (#vspec: _)
  (f: idxfn_t vspec bool)
  (il: verifiable_log vspec)
  : verifiable_log vspec

val map (#vspec:_) (#b:eqtype)
  (f: idxfn_t vspec b)
  (il: verifiable_log vspec)
  : interleaving b

val idxfn_from_tfn
  (#vspec:_)
  (#b:_)
  (tfn: T.idxfn_t vspec b)
  : idxfn_t vspec b

(* this lemma defines the output of the idxfn as running the tfn on the thread at the index
 * specified by the interleaving *)
val lemma_idxfn
  (#vspec:_)
  (#b:_)
  (tfn: T.idxfn_t vspec b)
  (il: verifiable_log vspec)
  (i: seq_index il)
  : Lemma (ensures (let ifn = idxfn_from_tfn tfn in
                    let ii = i2s_map il i in
                    ifn il i = G.idxfn tfn (to_glog il) ii))
          [SMTPat (idxfn_from_tfn tfn il i)]

(* the clock value at every index *)
let clock #vspec = idxfn_from_tfn (T.clock #vspec)

(* conditional index functions that are defined in some positions *)
val cond_idxfn_from_tfn (#vspec:_) (#b:_) (#f:_) (tfn: T.cond_idxfn_t #vspec b f)
  : cond_idxfn_t b (idxfn_from_tfn f)

