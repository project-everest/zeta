module Zeta.FilterMap

let rec indexed_filter_map (#a #b:_)
  (fm: filter_map_param_t a b)
  (s: seq a)
  : Tot (seq b)
    (decreases length s)
  = let n = length s in
    if n = 0
    then empty #b
    else
      let s' = prefix s (n - 1) in
      let ms' = indexed_filter_map fm s' in
      if fm.f s
      then append1 ms' (fm.m s)
      else ms'

let rec indexed_filter_map_map (#a #b:_)
  (fm: filter_map_param_t a b)
  (s: seq a)
  (i: seq_index s {fsat fm s i})
  : Tot(j: (seq_index (indexed_filter_map fm s)) {let fms = indexed_filter_map fm s in
                                              index fms j == map fm s i})
    (decreases (length s))
  = let n = length s - 1 in
    let s' = prefix s n in
    let ms' = indexed_filter_map fm s' in
    if i = n
    then length ms'
    else indexed_filter_map_map fm s' i

let rec indexed_filter_map_invmap (#a #b:_)
  (fm: filter_map_param_t a b)
  (s: seq a)
  (j: seq_index (indexed_filter_map fm s))
  : Tot (i:(seq_index s){ fsat fm s i /\ indexed_filter_map_map fm s i = j })
    (decreases (length s))
  = let n = length s - 1 in
    let s' = prefix s n in
    let ms' = indexed_filter_map fm s' in
    if j = length ms'
    then n
    else indexed_filter_map_invmap fm s' j

let rec lemma_indexed_filter_map (#a #b:_)
  (fm: filter_map_param_t a b)
  (s: seq a)
  (i: seq_index s {fsat fm s i})
  : Lemma (ensures (let j = indexed_filter_map_map fm s i in
                    i = indexed_filter_map_invmap fm s j))
          (decreases (length s))
  = let n = length s - 1 in
    let s' = prefix s n in
    if i = n then ()
    else lemma_indexed_filter_map fm s' i

let lemma_filter_map_extend_sat
  (#a #b:_)
  (fm: filter_map_param_t a b)
  (s: seq a {length s > 0 /\ fm.f s})
  : Lemma (ensures (let fms = indexed_filter_map fm s in
                    let fms' = indexed_filter_map fm (hprefix s) in
                    let me = fm.m s in
                    fms == append1 fms' me))
          (decreases length s)
  = ()

let lemma_filter_map_extend_unsat
  (#a #b:_)
  (fm: filter_map_param_t a b)
  (s: seq a {length s > 0 /\ not (fm.f s)})
  : Lemma (ensures (let fms = indexed_filter_map fm s in
                    let fms' = indexed_filter_map fm (hprefix s) in
                    fms == fms'))
  = ()

let lemma_filter_map_empty
  (#a #b:_)
  (fm: filter_map_param_t a b)
  (s: seq a {length s = 0})
  : Lemma (ensures length (indexed_filter_map fm s) = 0)
  = ()
