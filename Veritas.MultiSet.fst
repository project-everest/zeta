module Veritas.MultiSet

let mset (a:eqtype):Type0 = admit()

let equal (#a:eqtype) (s1:mset a) (s2:mset a): Tot bool = admit()

let mem (#a:eqtype) (x:a) (s:mset a): Tot nat = admit()

(* empty set *)
let empty (#a:eqtype): Tot (mset a) = admit()

let lemma_empty_implies_notmem (#a: eqtype) (s: mset a) (x: a):
  Lemma (requires (is_empty s))
        (ensures (~ (contains s x))) = admit()

(* construct a multiset given a sequence *)
let seq2mset (#a:eqtype) (s: seq a): Tot (mset a) = admit()
