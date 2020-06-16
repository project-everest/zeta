module Veritas.MultiSet

let mset (a:eqtype):Type0 = admit()

let mem (#a:eqtype) (x:a) (s:mset a): Tot nat = admit()

let equal (#a:eqtype) (s1:mset a) (s2:mset a): Tot bool = admit()

let lemma_eq_intro (#a:eqtype) (s1 s2:mset a): 
  Lemma (requires (forall (x:a). (mem x s1 = mem x s2)))
        (ensures (equal s1 s2)) = admit()

let lemma_eq_refl (#a:eqtype) (s1 s2: mset a):
  Lemma (requires (s1 == s2))
        (ensures (equal s1 s2)) = admit()

let lemma_eq_elim (#a:eqtype) (s1 s2: mset a):
  Lemma (requires (equal s1 s2))
        (ensures (s1 == s2)) = admit()

(* empty set *)
let empty (#a:eqtype): Tot (mset a) = admit()

let lemma_empty_implies_notmem (#a: eqtype) (s: mset a) (x: a):
  Lemma (requires (is_empty s))
        (ensures (~ (contains s x))) = admit()

(* construct a multiset given a sequence *)
let seq2mset (#a:eqtype) (s: seq a): Tot (mset a) = admit()
