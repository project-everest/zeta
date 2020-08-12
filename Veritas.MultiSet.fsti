module Veritas.MultiSet

open FStar.Seq

val mset (a:eqtype): Type0

(* membership: how many copies of x are in multiset s *)
val mem (#a:eqtype) (x:a) (s:mset a): Tot nat

(* equality of two multisets *)
val equal (#a:eqtype) (s1 s2:mset a): Tot prop

val lemma_eq_intro (#a:eqtype) (s1 s2:mset a): 
  Lemma (requires (forall (x:a). (mem x s1 = mem x s2)))
        (ensures (equal s1 s2))

val lemma_eq_refl (#a:eqtype) (s1 s2: mset a):
  Lemma (requires (s1 == s2))
        (ensures (equal s1 s2))

val lemma_eq_elim (#a:eqtype) (s1 s2: mset a):
  Lemma (requires (equal s1 s2))
        (ensures (s1 == s2))

(* empty set *)
val empty (#a:eqtype): Tot (mset a)

(* construct a multiset given a sequence *)
val seq2mset (#a:eqtype) (s: seq a): Tot (mset a)

(* count of an element in seq s is its membership count in its corresponding multiset *)
val lemma_count_mem (#a:eqtype) (s: seq a) (x: a):
  Lemma (count x s = mem x (seq2mset s))

(* union of two multisets *)
val union (#a:eqtype) (s1 s2: mset a): Tot (mset a)

(* the membership count of an element in a union of two multisets is 
 * the sum of its membership counts in the two sets *)
val lemma_union_count (#a:eqtype) (s1 s2: mset a) (x: a):
  Lemma (mem x (union s1 s2) = (mem x s1) + (mem x s2))

val lemma_union_comm (#a:eqtype) (s1 s2: mset a):
  Lemma (union s1 s2 == union s2 s1)

val lemma_union_assoc (#a:eqtype) (s1 s2 s3: mset a):
  Lemma (union (union s1 s2) s3 == union s1 (union s2 s3))

(* append of two sequences corresponds to the union in multiset domain *)
val lemma_union_append (#a:eqtype) (s1 s2: seq a):
  Lemma (seq2mset (append s1 s2) == union (seq2mset s1) (seq2mset s2))

