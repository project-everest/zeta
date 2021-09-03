module Zeta.IdxFn

let conj_is_idxfn (#gs:_) (f1 f2: idxfn_t gs bool)
  : Lemma (ensures (prefix_property (conj f1 f2)))
  = ()

let rec filter_map (#gs #b:_)
  (fm: fm_t gs b)
  (s: gs.seq_t)
  : Tot (seq b)
    (decreases gs.length s)
  = let n = gs.length s in
    if n = 0
    then empty #b
    else
      let s' = gs.prefix s (n - 1) in
      let ms' = filter_map fm s' in
      if fm.f s (n-1)
      then append1 ms' (fm.m s (n - 1))
      else ms'

let rec filter_map_map (#gs #b:_)
  (fm: fm_t gs b)
  (s: gs.seq_t)
  (i: seq_index s {fm.f s i})
  : Tot(j: (SA.seq_index (filter_map fm s)) {index (filter_map fm s) j == fm.m s i})
    (decreases (gs.length s))
  = let n = gs.length s - 1 in
    let s' = gs.prefix s n in
    let ms' = filter_map fm s' in
    if i = n
    then length ms'
    else filter_map_map fm s' i

let rec filter_map_map_prefix_property (#gs #b:_)
  (fm: fm_t gs b)
  (s: gs.seq_t)
  (i: seq_index s {fm.f s i})
  (j: nat{j <= gs.length s /\ j > i})
  : Lemma (ensures (filter_map_map fm s i = filter_map_map fm (gs.prefix s j) i))
          (decreases (gs.length s))
  = let n = gs.length s - 1 in
    let s' = gs.prefix s n in
    if i = n then ()
    else if j = gs.length s then ()
    else filter_map_map_prefix_property fm s' i j

let rec lemma_filter_map_map_monotonic (#gs #b:_)
  (fm: fm_t gs b)
  (s: gs.seq_t)
  (i1 i2: (i:seq_index s {fm.f s i}))
  : Lemma (ensures (i1 < i2 ==> filter_map_map fm s i1 < filter_map_map fm s i2))
          (decreases gs.length s)
  = let n = gs.length s - 1 in
    let s' = gs.prefix s n in
    if i1 >= i2 then ()
    else if i2 = n then ()
    else
      lemma_filter_map_map_monotonic fm s' i1 i2

let rec filter_map_invmap (#gs #b:_)
  (fm: fm_t gs b)
  (s: gs.seq_t)
  (j: SA.seq_index (filter_map fm s))
  : Tot(i:(seq_index s){fm.f s i /\ filter_map_map fm s i = j })
    (decreases (gs.length s))
  = let n = gs.length s - 1 in
    let s' = gs.prefix s n in
    let ms' = filter_map fm s' in
    if j = length ms'
    then n
    else filter_map_invmap fm s' j

let rec lemma_filter_map (#gs #b:_)
  (fm: fm_t gs b)
  (s: gs.seq_t)
  (i: seq_index s {fm.f s i})
  : Lemma (ensures (let j = filter_map_map fm s i in
                    i = filter_map_invmap fm s j))
          (decreases (gs.length s))
  = let n = gs.length s - 1 in
    let s' = gs.prefix s n in
    if i = n then ()
    else lemma_filter_map fm s' i

let filter_map_invmap_monotonic (#gs #b:_)
  (fm: fm_t gs b)
  (s: gs.seq_t)
  (j1 j2: SA.seq_index (filter_map fm s))
  : Lemma (ensures (j1 < j2 ==> filter_map_invmap fm s j1 < filter_map_invmap fm s j2))
  = if j1 >= j2 then ()
    else
      let i1 = filter_map_invmap fm s j1 in
      let i2 = filter_map_invmap fm s j2 in
      lemma_filter_map_map_monotonic fm s i1 i2;
      lemma_filter_map_map_monotonic fm s i2 i1

let lemma_filter_map_extend_sat
  (#gs:_)
  (#b:eqtype)
  (fm: fm_t gs b)
  (s: gs.seq_t {gs.length s > 0 /\ fm.f s (gs.length s - 1)})
  : Lemma (ensures (let fms = filter_map fm s in
                    let fms' = filter_map fm (gs.prefix s (gs.length s - 1)) in
                    let me = fm.m s (gs.length s - 1) in
                    fms == SA.append1 fms' me))
  = ()

let lemma_filter_map_extend_unsat
  (#gs:_)
  (#b:eqtype)
  (fm: fm_t gs b)
  (s: gs.seq_t {gs.length s > 0 /\ not (fm.f s (gs.length s - 1))})
  : Lemma (ensures (let fms = filter_map fm s in
                    let fms' = filter_map fm (gs.prefix s (gs.length s - 1)) in
                    fms == fms'))
  = ()

let lemma_filter_map_empty
  (#gs:_)
  (#b:eqtype)
  (fm: fm_t gs b)
  (s: gs.seq_t  {gs.length s = 0})
  : Lemma (ensures length (filter_map fm s) = 0)
  = ()

let rec lemma_filter_map_invmap_greater (#gs #b:_)
  (fm: fm_t gs b)
  (s: gs.seq_t)
  (j: SA.seq_index (filter_map fm s))
  : Lemma (ensures (filter_map_invmap fm s j >= j))
          (decreases j)
  = if j = 0 then ()
    else (
      lemma_filter_map_invmap_greater fm s (j - 1);
      filter_map_invmap_monotonic fm s (j - 1) j
    )

let rec lemma_map_map_greater (#gs #b:_)
  (m: idxfn_t gs b)
  (s: gs.seq_t)
  (i: seq_index s)
  : Lemma (ensures (let fm = map_fm m in
                    filter_map_map fm s i >= i))
          (decreases i)
  = let fm = map_fm m in
    if i = 0 then ()
    else (
      lemma_filter_map_map_monotonic fm s (i - 1) i;
      lemma_map_map_greater m s (i - 1)
    )

let lemma_map_length (#gs:_) (#b:_) (m: idxfn_t gs b) (s: gs.seq_t)
  : Lemma (ensures (length (map m s) = gs.length s))
  = let fm = map_fm m in
    if gs.length s = 0 then ()
    else (
      lemma_map_map_greater m s (gs.length s - 1);
      assert(length (map m s) >= gs.length s);
      lemma_filter_map_invmap_greater fm s (length (map m s) - 1)
    )

let lemma_map_map
  (#gs:_)
  (#b:_)
  (m: idxfn_t gs b)
  (s: gs.seq_t)
  (i: seq_index s)
  : Lemma (ensures (let fm = map_fm m in
                    filter_map_map fm s i = i))
  = let fm = map_fm m in
    lemma_map_map_greater m s i;
    lemma_filter_map_invmap_greater fm s (filter_map_map fm s i)
