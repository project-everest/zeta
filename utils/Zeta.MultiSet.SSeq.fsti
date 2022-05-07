module Zeta.MultiSet.SSeq

(* TODO: Merge this to Zeta.MultiSet.fsti ... it currently changes so frequently and breaks proofs in
 * MultiSet ... it is helpful to keep it separate temporarily *)

open Zeta.SSeq
open Zeta.MultiSet
open Zeta.Interleave

module S = FStar.Seq
module SA = Zeta.SeqAux

/// Construct a multiset from a seq of sequences

val sseq2mset (#a:eqtype) (#f:cmp a) (s:sseq a) : mset a f

val lemma_interleaving_multiset (#a:_) (#f:cmp a) (#n:_) (il: interleaving a n)
  : Lemma (ensures (seq2mset #_ #f (i_seq il) == sseq2mset (s_seq il)))

val union_all (#a:eqtype) (#f: cmp a) (s: S.seq (mset a f))
  : mset a f

val union_all_empty (#a: eqtype) (#f: cmp a) (s: S.seq (mset a f){ S.length s = 0 })
  : Lemma (ensures (union_all s == empty #a #f))

val union_all_snoc (#a: eqtype) (#f: _) (s: Seq.seq (Zeta.MultiSet.mset a f) {Seq.length s > 0})
  : Lemma (ensures (let prefix, last = Seq.un_snoc s in
                    union_all s == Zeta.MultiSet.union last (union_all prefix)))

val union_all_sseq (#a: eqtype) (#f: cmp a) (s: sseq a)
  : Lemma (ensures (let ms1: mset a f = sseq2mset s in
                    let sms = S.init (S.length s) (fun i -> seq2mset (S.index s i)) in
                    let ms2: mset a f = union_all sms in
                    ms1 == ms2))
