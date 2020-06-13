module Veritas.MultiSet

open FStar.Seq

val mset (a:eqtype): Type0

val equal (#a:eqtype) (s1:mset a) (s2:mset a): Tot bool

(* membership: how many copies of x are in multiset s *)
val mem (#a:eqtype) (x:a) (s:mset a): Tot nat

(* empty set *)
val empty (#a:eqtype): Tot (mset a)

(* does a multiset contain an element x *)
let contains (#a:eqtype) (s:mset a) (x:a) = mem x s = 0 

let is_empty (#a:eqtype) (s:mset a) = 
  equal s empty

(* the empty set does not contain anything *)
val lemma_empty_implies_notmem (#a: eqtype) (s: mset a) (x: a):
  Lemma (requires (is_empty s))
        (ensures (~ (contains s x)))

(* construct a multiset given a sequence *)
val seq2mset (#a:eqtype) (s: seq a): Tot (mset a)
