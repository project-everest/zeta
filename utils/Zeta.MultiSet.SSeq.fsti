module Zeta.MultiSet.SSeq

(* TODO: Merge this to Zeta.MultiSet.fsti ... it currently changes so frequently and breaks proofs in
 * MultiSet ... it is helpful to keep it separate temporarily *)

open Zeta.SSeq
open Zeta.MultiSet

/// Construct a multiset from a seq of sequences

val sseq2mset (#a:eqtype) (#f:cmp a) (s:sseq a) : mset a f
