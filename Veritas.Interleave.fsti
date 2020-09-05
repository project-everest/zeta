module Veritas.Interleave

open FStar.Seq
open FStar.Squash
open Veritas.SeqAux

module S = FStar.Seq
module SA = Veritas.SeqAux

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

(* 
 * interleaving: a triple that holds interleaved sequence, source sequences, and 
 * proof of interleaving *
 *)
noeq type interleaving (a:eqtype) = 
  | IL: s:seq a -> ss: sseq a -> prf:interleave s ss -> interleaving a

(* interleaved sequence *)
let i_seq (#a:eqtype) (il: interleaving a): seq a = 
  IL?.s il

(* source sequences *)
let s_seq (#a:eqtype) (il: interleaving a): sseq a = 
  IL?.ss il

let lemma_interleaving_correct (#a:eqtype) (il:interleaving a):
  Lemma (interleave (i_seq il) (s_seq il)) = 
  return_squash (IL?.prf il)

let length (#a:eqtype) (il: interleaving a): nat = 
  S.length (i_seq il)

let seq_index (#a:eqtype) (il: interleaving a) = i:nat{i < length il}

let index (#a: eqtype) (il: interleaving a) (i: seq_index il): a =
  (index (i_seq il) i)

val i2s_map (#a:eqtype) (il:interleaving a) (i:seq_index il): 
  (si:sseq_index (s_seq il){index il i = indexss (s_seq il) si})

val s2i_map (#a:eqtype) (il:interleaving a) (si: sseq_index (s_seq il)):
  (i:seq_index il{index il i = indexss (s_seq il) si /\
                  i2s_map il i = si})

val lemma_i2s_s2i (#a:eqtype) (il:interleaving a) (i:seq_index il):
  Lemma (requires True)
        (ensures (s2i_map il (i2s_map il i) = i))
        [SMTPat (i2s_map il i)]

val prefix (#a:eqtype) (il: interleaving a) (i:nat{i <= length il}): 
  Tot (il':interleaving a{i_seq il' = SA.prefix (i_seq il) i /\ 
                          S.length (s_seq il) = S.length (s_seq il')})

let hprefix (#a:eqtype) (il:interleaving a {length il > 0}): interleaving a =
  prefix il (length il - 1)

let telem (#a:eqtype) (il:interleaving a {length il > 0}): a =
  SA.telem (i_seq il)

val lemma_prefix_index (#a:eqtype) (il:interleaving a) (i:nat{i <= length il}) (j:nat{j < i}):
  Lemma (requires True)
        (ensures (index (prefix il i) j = index il j))
        [SMTPat (index (prefix il i) j)]

val lemma_prefix_prefix (#a:eqtype) (il:interleaving a) (i:nat{i <= length il}) (j:nat{j <= i}):
  Lemma (requires (True))
        (ensures (prefix (prefix il i) j == prefix il j))
        [SMTPat (prefix (prefix il i) j)]

val filter (#a:eqtype) (f:a -> bool) (il:interleaving a): interleaving a

(* every component sequence j of a prefix of il is a prefix of the corresponding component sequence of il *)
val lemma_prefix_interleaving (#a:eqtype) 
  (il: interleaving a) 
  (i:nat{ i <= length il}) 
  (j:nat{j < S.length (s_seq il)}):
  Lemma (SA.is_prefix (S.index (s_seq il) j) 
                      (S.index (s_seq (prefix il i)) j))
