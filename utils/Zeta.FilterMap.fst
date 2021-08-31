module Zeta.FilterMap

let rec filter_map (#a #b:_)
  (fm: fm_t a b)
  (s: seq a)
  : Tot (seq b)
    (decreases length s)
  = let n = length s in
    if n = 0
    then empty #b
    else
      let s' = prefix s (n - 1) in
      let ms' = filter_map fm s' in
      if fm.f (telem s)
      then append1 ms' (fm.m s (n - 1))
      else ms'

let rec filter_map_map (#a #b:_)
  (fm: fm_t a b)
  (s: seq a)
  (i: seq_index s {fm.f (index s i)})
  : Tot(j: (seq_index (filter_map fm s)) {index (filter_map fm s) j == fm.m s i})
    (decreases (length s))
  = let n = length s - 1 in
    let s' = prefix s n in
    let ms' = filter_map fm s' in
    if i = n
    then length ms'
    else filter_map_map fm s' i

let rec filter_map_invmap (#a #b:_)
  (fm: fm_t a b)
  (s: seq a)
  (j: seq_index (filter_map fm s))
  : Tot(i:(seq_index s){ fm.f (index s i) /\ filter_map_map fm s i = j })
    (decreases (length s))
  = let n = length s - 1 in
    let s' = prefix s n in
    let ms' = filter_map fm s' in
    if j = length ms'
    then n
    else filter_map_invmap fm s' j

let rec lemma_filter_map (#a #b:_)
  (fm: fm_t a b)
  (s: seq a)
  (i: seq_index s {fm.f (index s i)})
  : Lemma (ensures (let j = filter_map_map fm s i in
                    i = filter_map_invmap fm s j))
          (decreases (length s))
  = let n = length s - 1 in
    let s' = prefix s n in
    if i = n then ()
    else lemma_filter_map fm s' i

let lemma_filter_map_extend_sat
  (#a:_)
  (#b:eqtype)
  (fm: fm_t a b)
  (s: seq a {length s > 0 /\ fm.f (telem s)})
  : Lemma (ensures (let fms = filter_map fm s in
                    let fms' = filter_map fm (hprefix s) in
                    let me = fm.m s (length s - 1) in
                    fms == append1 fms' me))
  = ()

let lemma_filter_map_extend_unsat
  (#a:_)
  (#b:eqtype)
  (fm: fm_t a b)
  (s: seq a {length s > 0 /\ not (fm.f (telem s))})
  : Lemma (ensures (let fms = filter_map fm s in
                    let fms' = filter_map fm (hprefix s) in
                    fms == fms'))
  = ()

let lemma_filter_map_empty
  (#a:_)
  (#b:eqtype)
  (fm: fm_t a b)
  (s: seq a {length s = 0})
  : Lemma (ensures length (filter_map fm s) = 0)
  = ()

let rec ssfilter_map (#a #b:_)
  (fm: ssfm_t a b)
  (s: sseq a)
  : Tot (s':sseq b {length s' = length s})
    (decreases (length s))
  = let n = length s in
    if n = 0 then empty #(seq b)
    else
      let fmss' = ssfilter_map fm (prefix s (n-1)) in
      let fmi = to_fm_t fm (n - 1) in
      let fms = filter_map fmi (index s (n-1)) in
      append1 fmss' fms
