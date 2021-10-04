module Zeta.SeqIdx

let exists_elems_with_prop_comp (#a:_) (p: a -> bool) (s: seq a)
  : b:bool {b <==> exists_elems_with_prop p s}
  = admit()

let exists_elems_with_prop_intro (#a:_) (p: a -> bool) (s: seq a) (i: seq_index s{p (index s i)})
  : Lemma (ensures (exists_elems_with_prop p s))
  = admit()

let last_idx (#a:_) (p: a -> bool) (s: seq a {exists_elems_with_prop p s})
  : i:seq_index s{p (index s i)}
  = admit()

let last_idx_snoc (#a:_) (p: a -> bool) (s: seq a {length s > 0})
  : Lemma (ensures (let i = length s - 1 in
                    let s' = prefix s i in
                    p (index s i) /\ last_idx p s = i \/
                    ~ (p (index s i))  /\
                    (exists_elems_with_prop p s <==> exists_elems_with_prop p s') /\
                    (exists_elems_with_prop p s' ==> last_idx p s = last_idx p s')))
  = admit()

let last_idx_correct (#a:_) (p: a -> bool)
  (s: seq a{exists_elems_with_prop p s})
  (i: seq_index s)
  : Lemma (ensures ((i > last_idx p s ==> ~ (p (index s i))) /\
                    (p (index s i) ==> i <= last_idx p s)))
  = admit()

let next_idx (#a:_) (p: a -> bool)
  (s: seq a {exists_elems_with_prop p s})
  (i: seq_index s{i < last_idx p s})
  : j:seq_index s{p (index s j) /\ j > i /\ j <= (last_idx p s)}
  = admit()

let next_idx_correct (#a:_) (p: a -> bool)
  (s: seq a {exists_elems_with_prop p s})
  (i: seq_index s {i < last_idx p s})
  : Lemma (ensures (let j = next_idx p s i in
                    let s' = prefix s j in
                    exists_elems_with_prop p s' ==> last_idx p s' <= i))
  = admit()
