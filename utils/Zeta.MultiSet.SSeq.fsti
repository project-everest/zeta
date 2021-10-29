module Zeta.MultiSet.SSeq

(* TODO: Merge this to Zeta.MultiSet.fsti ... it currently changes so frequently and breaks proofs in
 * MultiSet ... it is helpful to keep it separate temporarily *)

open Zeta.SSeq
open Zeta.MultiSet
open Zeta.Interleave

/// Construct a multiset from a seq of sequences

val sseq2mset (#a:eqtype) (#f:cmp a) (s:sseq a) : mset a f

val lemma_interleaving_multiset (#a:_) (#f:cmp a) (#n:_) (il: interleaving a n)
  : Lemma (ensures (seq2mset #_ #f (i_seq il) == sseq2mset (s_seq il)))
