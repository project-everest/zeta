module Veritas.MultiSet

let mset (a:eqtype):Type0 = admit()

let mem (#a:eqtype) (x:a) (s:mset a): Tot nat = admit()

let equal (#a:eqtype) (s1:mset a) (s2:mset a): Tot prop = admit()

let lemma_eq_intro (#a:eqtype) (s1 s2:mset a): 
  Lemma (requires (forall (x:a). (mem x s1 = mem x s2)))
        (ensures (equal s1 s2)) = admit()

let lemma_eq_refl (#a:eqtype) (s1 s2: mset a):
  Lemma (requires (s1 == s2))
        (ensures (equal s1 s2)) = admit()

let lemma_eq_elim (#a:eqtype) (s1 s2: mset a):
  Lemma (requires (equal s1 s2))
        (ensures (s1 == s2)) = admit()

let lemma_not_equal (#a:eqtype) (s1 s2: mset a) (x: a):
  Lemma (requires (mem x s1 <> mem x s2))
        (ensures (~(s1 == s2))) = admit()

(* size of a multi set *)
let size (#a:eqtype) (s: mset a): nat = admit()

(* empty set *)
let empty (#a:eqtype): Tot (mset a) = admit()

let create (#a:eqtype) (x:a) (m:nat): Tot (mset a) = admit()

(* construct a multiset given a sequence *)
let seq2mset (#a:eqtype) (s: seq a): Tot (mset a) = admit()

let lemma_count_mem (#a:eqtype) (s: seq a) (x: a):
  Lemma (count x s = mem x (seq2mset s)) = admit()

(* union of two multisets *)
let union (#a:eqtype) (s1 s2: mset a): Tot (mset a) = admit()

(* the membership count of an element in a union of two multisets is 
 * the sum of its membership counts in the two sets *)
let lemma_union_count (#a:eqtype) (s1 s2: mset a) (x: a):
  Lemma (mem x (union s1 s2) = (mem x s1) + (mem x s2)) = admit()

let lemma_union_comm (#a:eqtype) (s1 s2: mset a):
  Lemma (union s1 s2 == union s2 s1) = admit()

let lemma_union_assoc (#a:eqtype) (s1 s2 s3: mset a):
  Lemma (union (union s1 s2) s3 == union s1 (union s2 s3)) = admit()

(* append of two sequences corresponds to the union in multiset domain *)
let lemma_union_append (#a:eqtype) (s1 s2: seq a):
  Lemma (seq2mset (append s1 s2) == union (seq2mset s1) (seq2mset s2)) = admit()

(* if one multiset s1 is larger than the other (s2) we can find an element whose membership in s1 is larger *)
let diff_elem (#a:eqtype) (s1: mset a) (s2: mset a{size s1 > size s2}): (x:a{mem x s1 > mem x s2}) = admit()

(* add an element to a multiset *)
let add_elem (#a:eqtype) (s: mset a) (x:a): mset a = admit()

(* add increases the size by 1 *)
let lemma_add_size (#a:eqtype) (s:mset a) (x:a):
  Lemma (size (add_elem s x) = size s + 1) = admit()

