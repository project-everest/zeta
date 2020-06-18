module Veritas.MultiSet

open FStar.Seq

val mset (a:eqtype): Type0

(* membership: how many copies of x are in multiset s *)
val mem (#a:eqtype) (x:a) (s:mset a): Tot nat

(* equality of two multisets *)
val equal (#a:eqtype) (s1 s2:mset a): Tot bool

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

(* does a multiset contain an element x *)
let contains (#a:eqtype) (s:mset a) (x:a) = mem x s > 0 

let is_empty (#a:eqtype) (s:mset a): Tot bool = 
  equal s empty

(* the empty set does not contain anything *)
val lemma_empty_implies_notmem (#a: eqtype) (s: mset a) (x: a):
  Lemma (requires (is_empty s))
        (ensures (~ (contains s x)))

(* TODO: what connects boolean equality '=' and equal *)
val hasEq_lemma (a:Type):
  Lemma (requires (hasEq a)) 
        (ensures (hasEq (mset a))) 
        [SMTPat (hasEq  (mset a))]

(* construct a multiset given a sequence *)
val seq2mset (#a:eqtype) (s: seq a): Tot (mset a)
