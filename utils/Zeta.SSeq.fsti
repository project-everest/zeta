module Zeta.SSeq

open FStar.Seq
open Zeta.SeqAux

(* sequence of sequences *)
type sseq (a:Type) = seq (seq a)

(* an index into an element of sseq *)
type sseq_index (#a:Type) (ss: sseq a) =
  (ij:(nat * nat){(fst ij) < length ss /\
               (snd ij) < length (index ss (fst ij))})

(* retrieve an element of an sseq given its index *)
let indexss (#a:Type) (ss: sseq a) (ij: sseq_index ss): Tot a =
  let (i,j) = ij in
  index (index ss i) j

(* sum of lengths of all sequences in a sequence of seqs *)
val flat_length (#a:Type) (ss: sseq a)
  : Tot nat

(* flat length of an empty sseq *)
val lemma_flat_length_empty (#a:Type)
  : Lemma (flat_length (empty #(seq a)) = 0)

(* appending a singleton adds to the flat length *)
val lemma_flat_length_app1 (#a:Type) (ss: sseq a) (s: seq a)
  : Lemma (flat_length ss + length s = flat_length (append1 ss s))

(* appending adds to the flat length *)
val lemma_flat_length_app (#a:Type) (ss1 ss2: sseq a)
  : Lemma (flat_length ss1 + flat_length ss2 = flat_length (append ss1 ss2))

let sseq_extend (#a:eqtype) (ss: sseq a) (x:a) (i:seq_index ss): sseq a =
  let si = index ss i in
  let si' = append1 si x in
  upd ss i si'

val lemma_sseq_correct1 (#a:eqtype) (ss: sseq a) (x:a) (i:seq_index ss):
  Lemma (index (sseq_extend ss x i) i = append1 (index ss i) x)

val lemma_sseq_correct2 (#a:eqtype) (ss: sseq a) (x:a) (i:seq_index ss) (j:seq_index ss{j <> i}):
  Lemma (index (sseq_extend ss x i) j = index ss j)

val lemma_sseq_extend_len (#a:eqtype) (ss: sseq a) (x:a) (i:seq_index ss):
  Lemma (ensures (flat_length (sseq_extend ss x i) = 1 + flat_length ss))
