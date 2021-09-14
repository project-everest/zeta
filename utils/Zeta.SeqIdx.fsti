module Zeta.SeqIdx

open FStar.Seq
open Zeta.SeqAux

let exists_elems_with_prop (#a:_) (p: a -> bool) (s: seq a)
  = exists i. p (index s i)

val exists_elems_with_prop_comp (#a:_) (p: a -> bool) (s: seq a)
  : b:bool {b <==> exists_elems_with_prop p s}

val exists_elems_with_prop_intro (#a:_) (p: a -> bool) (s: seq a) (i: seq_index s{p (index s i)})
  : Lemma (ensures (exists_elems_with_prop p s))

val last_idx (#a:_) (p: a -> bool) (s: seq a {exists_elems_with_prop p s})
  : i:seq_index s{p (index s i)}

val last_idx_snoc (#a:_) (p: a -> bool) (s: seq a {exists_elems_with_prop p s /\ length s > 0})
  : Lemma (ensures (let i = length s - 1 in
                    let s' = prefix s i in
                    p (index s i) /\ last_idx p s = i \/
                    ~ (p (index s i)) /\ exists_elems_with_prop p s' /\
                    last_idx p s = last_idx p s'))

val last_idx_correct (#a:_) (p: a -> bool)
  (s: seq a{exists_elems_with_prop p s})
  (i: seq_index s)
  : Lemma (ensures ((i > last_idx p s ==> ~ (p (index s i))) /\
                    (p (index s i) ==> i <= last_idx p s)))

