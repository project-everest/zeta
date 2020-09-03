module Veritas.MultiSet

open FStar.Seq
open Veritas.SeqAux

val mset (a:eqtype): Type0

(* membership: how many copies of x are in multiset s *)
val mem (#a:eqtype) (x:a) (s:mset a): Tot nat

(* does a multiset contain an element x *)
let contains (#a:eqtype) (x:a) (s:mset a) = 
  mem x s > 0

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

val lemma_not_equal (#a:eqtype) (s1 s2: mset a) (x: a):
  Lemma (requires (mem x s1 <> mem x s2))
        (ensures (~(s1 == s2)))

(* size of a multi set *)
val size (#a:eqtype) (s: mset a): nat

(* empty set *)
val empty (#a:eqtype): Tot (mset a)

(* create a multiset of m copies of x *)
val create (#a:eqtype) (x:a) (m:nat): Tot (mset a)

(* construct a multiset given a sequence *)
val seq2mset (#a:eqtype) (s: seq a): Tot (mset a)

(* mapping from one sequence to an other *)
let smap (#a:eqtype) (s1 s2: seq a) = f: (seq_index s1 -> seq_index s2)
  { forall (i: seq_index s1). index s1 i = index s2 (f i) }

let into_smap (#a:eqtype) (s1 s2: seq a)  = f: smap s1 s2
  { forall (i: seq_index s1). forall (j: seq_index s1{i <> j}). f i <> f j }

val lemma_mset_bijection (#a:eqtype) (s1 s2: seq a) (f12: into_smap s1 s2) (f21: into_smap s2 s1):
  Lemma (seq2mset s1 == seq2mset s2)

(* count of an element in seq s is its membership count in its corresponding multiset *)
val lemma_count_mem (#a:eqtype) (s: seq a) (x: a):
  Lemma (count x s = mem x (seq2mset s))

(* an element at the i'th index of a sequence is in the multiset *)
val lemma_seq_elem (#a:eqtype) (s: seq a) (i:nat{i < length s}):
  Lemma (contains (index s i) (seq2mset s))

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

(* a multiset is a pure set if there is at most one copy of each element *)
let is_set (#a:eqtype) (s: mset a) = forall (x:a). mem x s <= 1

(* if one multiset s1 is larger than the other (s2) we can find an element whose membership in s1 is larger *)
val diff_elem (#a:eqtype) (s1: mset a) (s2: mset a{size s1 > size s2}): (x:a{mem x s1 > mem x s2})

(* add an element to a multiset *)
val add_elem (#a:eqtype) (s: mset a) (x:a): mset a

(* add increases the size by 1 *)
val lemma_add_size (#a:eqtype) (s:mset a) (x:a):
  Lemma (requires True)
        (ensures (size (add_elem s x) = size s + 1))
        [SMTPat (add_elem s x)]
