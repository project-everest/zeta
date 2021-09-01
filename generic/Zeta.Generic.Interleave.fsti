module Zeta.Generic.Interleave

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
let to_glog #vspec (il: ilog vspec): G.vlog _
  = I.s_seq il

let seq_index #vspec (il: ilog vspec) = I.seq_index il

let prefix #vspec (il: ilog vspec) = I.prefix il

(* an interleaving is verifiable is the source logs are verifiable *)
let verifiable #vspec (il: ilog vspec) =
  G.verifiable (to_glog il)

let verifiable_log vspec = il:ilog vspec {verifiable il}

val lemma_prefix_verifiable (#vspec:_) (il:verifiable_log vspec) (i:nat{i <= I.length il}):
  Lemma (ensures (verifiable (I.prefix il i)))
        [SMTPat (I.prefix il i)]

(* an index function is a function that returns a value at every index of the interleaved log *)
(* a class of index functions we are interested in are index functions that derive from index
 * functions of the thread log *)
let idxfn (#vspec:_) (#b:_) (tfn: idxfn_t vspec b) (il: verifiable_log vspec) (i: seq_index il)
  = let j = i2s_map il i in
    G.idxfn tfn (to_glog il) j

let prefix_property #vspec #b (tfn: idxfn_t vspec b)
  = forall (il: verifiable_log vspec) (i: nat) (j:nat).
     {:pattern idxfn tfn (prefix il j) i}
      j <= I.length il ==>
      i < j ==>
      idxfn tfn il i = idxfn tfn (prefix il j) i

val lemma_idxfn_prefix_property
  (#vspec:_)
  (#b:_)
  (tfn: idxfn_t vspec b)
  : Lemma (ensures (prefix_property tfn))
          [SMTPat (idxfn tfn)]

(* the clock value at every index *)
let clock #vspec = idxfn (T.clock #vspec)

(* conditional index functions that are defined in some positions *)
let cond_idxfn (#vspec:_) (#b:_) (#f:_) (tfn: cond_idxfn_t #vspec b f)
  (il: verifiable_log vspec) (i: seq_index il {idxfn f il i})
  = let j = i2s_map il i in
    G.cond_idxfn tfn (to_glog il) j

