module Veritas.Interleave

open FStar.Seq
open Veritas.SeqAux

(* sequence of sequences *)
type sseq (a:Type) = seq (seq a)

(* sum of lengths of all sequences in a sequence of seqs *)
val flat_length (#a:Type) (ss: sseq a): Tot nat

(* flat length of an empty sseq *)
val lemma_flat_length_empty (#a:Type):
  Lemma (flat_length (empty #(seq a)) = 0)

(* appending a singleton adds to the flat length *)
val lemma_flat_length_app1 (#a:Type) (ss: sseq a) (s: seq a):
  Lemma (flat_length ss + length s = flat_length (append1 ss s))

(* appending adds to the flat length *)
val lemma_flat_length_app (#a:Type) (ss1 ss2: sseq a):
  Lemma (flat_length ss1 + flat_length ss2 = flat_length (append ss1 ss2))

(* interleaving of n sequences *)
val interleave (#a:eqtype): seq a -> ss:(seq (seq a)) -> Type 

(* if we have a proof of interleaving we can construct a mapping from 
 * interleaved sequence to the sources *)
val interleave_map (#a:eqtype) (s: seq a) (ss: seq (seq a)) 
     (prf:interleave #a s ss) (i: seq_index s): 
  Tot (j: (nat*nat){fst j < length ss /\
                 snd j < length (index ss (fst j)) /\
                 index (index ss (fst j)) (snd j) = index s i})

(* inverse of interleave map *)
val interleave_map_inv (#a:eqtype) (s: seq a) (ss: seq (seq a))
      (prf:interleave #a s ss) (i: seq_index ss) (j: seq_index (index ss i)): 
  Tot (k: seq_index s{index s k = index (index ss i) j})

(* length of an interleaving is the sum of the lengths of the individual sequences *)
val lemma_interleave_length (#a:eqtype) (s: seq a) (ss: seq (seq a){interleave s ss}):
  Lemma (length s = flat_length ss)

(* an interleave constructor that specifies the construction of 
 * an interleaving *)
type interleave_ctor (#a:eqtype) (ss: seq (seq a)) =
  (i: seq_index ss) -> (j: seq_index (index ss i)) -> k:nat{k < flat_length ss}

(* from an interleave_ constructor we can get an interleaving *)
val interleaved_seq (#a:eqtype) (ss: seq (seq a)) (ic: interleave_ctor ss):
  Tot (s: seq a{interleave s ss})

(* we can also construct a proof of interleaving *)
val interleaving_prf (#a: eqtype) (ss: seq (seq a)) (ic: interleave_ctor ss):
  Tot (interleave (interleaved_seq ss ic) ss)

(* sortedness of a sequence *)
type sorted (#a:Type) (lte: a -> a -> bool) (s: seq a) = 
  forall (i:seq_index s). i > 0 ==> index s (i - 1) `lte` index s i

(* sort-merge interleaving *)
val sort_merge (#a:eqtype) (lte: a-> a-> bool) 
               (ss: seq (seq a){forall (i:seq_index ss). sorted lte (index ss i)}): 
  Tot (interleave_ctor ss)

val lemma_sort_merge (#a:eqtype) (lte: a -> a -> bool)
  (ss: seq (seq a){forall (i: seq_index ss). sorted lte (index ss i)}):
  Lemma (requires (True))
        (ensures (sorted lte (interleaved_seq ss (sort_merge lte ss))))
        [SMTPat (sort_merge lte ss)]

