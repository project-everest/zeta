module Zeta.SeqIdx

open FStar.Classical

let rec find_last_elem_with_prop (#a:_) (p: a -> bool) (s: seq a)
  : Tot(o:option nat {o = None /\ (forall i. not (p (index s i))) \/
                Some? o /\ (let i = Some?.v o in
                           i < length s /\ p (index s i))})
    (decreases (length s))
  = if length s = 0 then None
    else
      let i = length s - 1 in
      let s' = prefix s i in
      let o = find_last_elem_with_prop p s' in
      if p (index s i) then
        Some i
      else if Some? o then o
      else
        let aux (j:_)
          : Lemma (ensures (not (p (index s j))))
          = if j < i then
              eliminate forall i. (not (p (index s' i)))
              with j
        in
        forall_intro aux;
        None

let exists_elems_with_prop_comp (#a:_) (p: a -> bool) (s: seq a)
  : b:bool {b <==> exists_elems_with_prop p s}
  = find_last_elem_with_prop p s <> None

let exists_elems_with_prop_intro (#a:_) (p: a -> bool) (s: seq a) (i: seq_index s{p (index s i)})
  : Lemma (ensures (exists_elems_with_prop p s))
  = ()

let last_idx (#a:_) (p: a -> bool) (s: seq a {exists_elems_with_prop p s})
  : i:seq_index s{p (index s i)}
  = Some?.v (find_last_elem_with_prop p s)

let last_idx_snoc (#a:_) (p: a -> bool) (s: seq a {length s > 0})
  : Lemma (ensures (let i = length s - 1 in
                    let s' = prefix s i in
                    p (index s i) /\ last_idx p s = i \/
                    ~ (p (index s i))  /\
                    (exists_elems_with_prop p s <==> exists_elems_with_prop p s') /\
                    (exists_elems_with_prop p s' ==> last_idx p s = last_idx p s')))
  = let o = find_last_elem_with_prop p s in
    ()

let rec last_idx_correct (#a:_) (p: a -> bool)
  (s: seq a{exists_elems_with_prop p s})
  (i: seq_index s)
  : Lemma (ensures ((i > last_idx p s ==> ~ (p (index s i))) /\
                    (p (index s i) ==> i <= last_idx p s)))
          (decreases (length s))
  = let n = length s in
    let s' = prefix s (n - 1) in
    last_idx_snoc p s;
    if i < n- 1 && not (p (index s (n-1))) then
      last_idx_correct p s' i

let rec next_idx (#a:_) (p: a -> bool)
  (s: seq a {exists_elems_with_prop p s})
  (i: seq_index s{i < last_idx p s})
  : Tot(j:seq_index s{p (index s j) /\ j > i /\ j <= (last_idx p s)})
    (decreases (length s - i))
  = let j = i + 1 in
    if p (index s j) then j
    else if j = last_idx p s then j
    else next_idx p s j

let rec next_idx_correct (#a:_) (p: a -> bool)
  (s: seq a {exists_elems_with_prop p s})
  (i: seq_index s {i < last_idx p s})
  : Lemma (ensures (let j = next_idx p s i in
                    let s' = prefix s j in
                    exists_elems_with_prop p s' ==> last_idx p s' <= i))
          (decreases (length s - i))
  = let j = i + 1 in
    if not (p (index s j)) && j < last_idx p s then
      next_idx_correct p s j
