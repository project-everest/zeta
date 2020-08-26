module Veritas.Interleave

open FStar.Seq
open Veritas.SeqAux

(* sequence of sequences *)
type sseq (a:Type) = seq (seq a)

(* an index into an element of sseq *)
type sseq_index (#a:Type) (ss: sseq a) = 
  (ij:(nat * nat){(fst ij) < length ss /\ 
                (snd ij) < length (index ss (fst ij))})

(* retrieve an element of an sseq given its index *)
val indexss (#a:Type) (ss: sseq a) (ij: sseq_index ss): Tot a

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
val interleave (#a:eqtype): seq a -> ss:sseq a -> Type0 

(* length of an interleaving is the sum of the lengths of the individual sequences *)
val lemma_interleave_length (#a:eqtype) (s: seq a) (ss: sseq a{interleave s ss}):
  Lemma (length s = flat_length ss)
  [SMTPat (interleave #a s ss)]

(* if we have a proof of interleaving we can construct a mapping from 
 * interleaved sequence to the sources *)
val interleave_map (#a:eqtype) (s: seq a) (ss: sseq a)
     (prf:interleave #a s ss) (i: seq_index s): 
  Tot (j: (sseq_index ss){indexss ss j = index s i})
  
(* inverse of interleave map *)
val interleave_map_inv (#a:eqtype) (s: seq a) (ss: sseq a)
      (prf:interleave #a s ss) (i: sseq_index ss):
  Tot (j: seq_index s{index s j = indexss ss i})

noeq type interleave_ctor (#a:eqtype) (ss: sseq a) = 
  | IntCtr: s: seq a -> prf: interleave s ss -> interleave_ctor ss

(* from an interleave_ constructor we can get an interleaving *)
let interleaved_seq (#a:eqtype) (ss: sseq a) (ic: interleave_ctor ss):
  Tot (s: seq a{interleave s ss}) = 
  match ic with
  | IntCtr s _ -> s

(* we can also construct a proof of interleaving *)
let interleaving_prf (#a: eqtype) (ss: sseq a) (ic: interleave_ctor ss):
  Tot (interleave (interleaved_seq ss ic) ss) = 
  match ic with
  | IntCtr _ prf -> prf

(* sortedness of a sequence *)
type sorted (#a:Type) (lte: a -> a -> bool) (s: seq a) = 
  forall (i:seq_index s). i > 0 ==> index s (i - 1) `lte` index s i

(* sort-merge interleaving *)
val sort_merge (#a:eqtype) (lte: a-> a-> bool) 
               (ss: sseq a{forall (i:seq_index ss). sorted lte (index ss i)}): 
  Tot (interleave_ctor ss)

val lemma_sort_merge (#a:eqtype) (lte: a -> a -> bool)
  (ss: sseq a{forall (i: seq_index ss). sorted lte (index ss i)}):
  Lemma (requires (True))
        (ensures (sorted lte (interleaved_seq ss (sort_merge lte ss))))
        [SMTPat (sort_merge lte ss)]

(* filter and interleaving commute (constructive version) *)
val lemma_filter_interleave_commute_prf (#a:eqtype) 
  (f:a -> bool) (s: seq a) (ss: sseq a) (prf: interleave s ss): 
  Tot (interleave (filter f s) (map (filter f) ss))

(* filter and interleaving commute *)
val lemma_filter_interleave_commute (#a:eqtype) (f:a -> bool) (s: seq a) (ss: sseq a{interleave s ss}):  
  Lemma (interleave (filter f s) (map (filter f) ss))

type idx_elem (#a:eqtype) (n:nat) = a * (i:nat{i < n})

let project_seq (#a:eqtype) (#n:nat) (s:seq (idx_elem #a n)): seq a
  = fst (unzip s)

val partition_idx_seq (#a:eqtype) (#n:nat) (s: seq (idx_elem #a n)):
  Tot (ss:sseq a{length ss = n})

val lemma_partition_idx_seq_interleaving (#a:eqtype) (#n:nat) (s: seq (idx_elem #a n)):
  Lemma (interleave (project_seq s) (partition_idx_seq s))

val lemma_partition_idx_prefix_comm 
  (#a:eqtype) (#n:nat) (s:seq (idx_elem #a n)) (i:nat{i <= length s}) (id:nat{id < n}):
  Lemma (is_prefix (index (partition_idx_seq s) id)
                   (index (partition_idx_seq (prefix s i)) id))

val lemma_partition_idx_extend1 (#a:eqtype) (#n:nat) (s: seq (idx_elem #a n){length s > 0}):
  Lemma (index (partition_idx_seq s) (snd (telem s)) = 
         append1 (index (partition_idx_seq (hprefix s)) (snd (telem s)))
                 (fst (telem s)))

val interleaved_idx_seq (#a:eqtype) (ss: sseq a) (ic: interleave_ctor ss):
  Tot (seq (idx_elem #a (length ss)))

val lemma_interleaved_idx_seq_correct (#a:eqtype) (ss: sseq a) (ic: interleave_ctor ss):
  Lemma (requires True)
        (ensures (partition_idx_seq (interleaved_idx_seq ss ic) = ss))
        [SMTPat (interleaved_idx_seq ss ic)]
