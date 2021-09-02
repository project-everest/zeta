module Zeta.FilterMap

let rec filter_map (#a #pred #b:_)
  (fm: fm_t a pred b)
  (s: seq a{pred s})
  : Tot (seq b)
    (decreases length s)
  = let n = length s in
    if n = 0
    then empty #b
    else
      let s' = prefix s (n - 1) in
      let ms' = filter_map fm s' in
      if fm.f s (n-1)
      then append1 ms' (fm.m s (n - 1))
      else ms'

let rec filter_map_map (#a #pred #b:_)
  (fm: fm_t a pred b)
  (s: seq a{pred s})
  (i: seq_index s {fm.f s i})
  : Tot(j: (seq_index (filter_map fm s)) {index (filter_map fm s) j == fm.m s i})
    (decreases (length s))
  = let n = length s - 1 in
    let s' = prefix s n in
    let ms' = filter_map fm s' in
    if i = n
    then length ms'
    else filter_map_map fm s' i

let rec filter_map_map_prefix_property (#a #pred #b:_)
  (fm: fm_t a pred b)
  (s: seq a{pred s})
  (i: seq_index s {fm.f s i})
  (j: nat{j <= length s /\ j > i})
  : Lemma (ensures (filter_map_map fm s i = filter_map_map fm (prefix s j) i))
          (decreases (length s))
  = let n = length s - 1 in
    let s' = prefix s n in
    if i = n then ()
    else if j = length s then ()
    else filter_map_map_prefix_property fm s' i j

let rec lemma_filter_map_map_monotonic (#a #pred #b:_)
  (fm: fm_t a pred b)
  (s: seq a{pred s})
  (i1 i2: (i:seq_index s {fm.f s i}))
  : Lemma (ensures (i1 < i2 ==> filter_map_map fm s i1 < filter_map_map fm s i2))
          (decreases length s)
  = let n = length s - 1 in
    let s' = prefix s n in
    if i1 >= i2 then ()
    else if i2 = n then ()
    else
      lemma_filter_map_map_monotonic fm s' i1 i2

let rec filter_map_invmap (#a #pred #b:_)
  (fm: fm_t a pred b)
  (s: seq a{pred s})
  (j: seq_index (filter_map fm s))
  : Tot(i:(seq_index s){ fm.f s i /\ filter_map_map fm s i = j })
    (decreases (length s))
  = let n = length s - 1 in
    let s' = prefix s n in
    let ms' = filter_map fm s' in
    if j = length ms'
    then n
    else filter_map_invmap fm s' j

let rec lemma_filter_map (#a #pred #b:_)
  (fm: fm_t a pred b)
  (s: seq a {pred s})
  (i: seq_index s {fm.f s i})
  : Lemma (ensures (let j = filter_map_map fm s i in
                    i = filter_map_invmap fm s j))
          (decreases (length s))
  = let n = length s - 1 in
    let s' = prefix s n in
    if i = n then ()
    else lemma_filter_map fm s' i

let filter_map_invmap_monotonic (#a #pred #b:_)
  (fm: fm_t a pred b)
  (s: seq a{pred s})
  (j1 j2: seq_index (filter_map fm s))
  : Lemma (ensures (j1 < j2 ==> filter_map_invmap fm s j1 < filter_map_invmap fm s j2))
  = if j1 >= j2 then ()
    else
      let i1 = filter_map_invmap fm s j1 in
      let i2 = filter_map_invmap fm s j2 in
      lemma_filter_map_map_monotonic fm s i1 i2;
      lemma_filter_map_map_monotonic fm s i2 i1

let lemma_filter_map_extend_sat
  (#a:_)
  (#pred:_)
  (#b:eqtype)
  (fm: fm_t a pred b)
  (s: seq a {pred s /\ length s > 0 /\ fm.f s (length s - 1)})
  : Lemma (ensures (let fms = filter_map fm s in
                    let fms' = filter_map fm (hprefix s) in
                    let me = fm.m s (length s - 1) in
                    fms == append1 fms' me))
  = ()

let lemma_filter_map_extend_unsat
  (#a:_)
  (#pred:_)
  (#b:eqtype)
  (fm: fm_t a pred b)
  (s: seq a {pred s /\ length s > 0 /\ not (fm.f s (length s - 1))})
  : Lemma (ensures (let fms = filter_map fm s in
                    let fms' = filter_map fm (hprefix s) in
                    fms == fms'))
  = ()

let lemma_filter_map_empty
  (#a:_)
  (#pred:_)
  (#b:eqtype)
  (fm: fm_t a pred b)
  (s: seq a {pred s /\ length s = 0})
  : Lemma (ensures length (filter_map fm s) = 0)
  = ()

