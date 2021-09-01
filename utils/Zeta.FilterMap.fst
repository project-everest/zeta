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
      if fm.f s (n-1)
      then append1 ms' (fm.m s (n - 1))
      else ms'

let rec filter_map_map (#a #b:_)
  (fm: fm_t a b)
  (s: seq a)
  (i: seq_index s {fm.f s i})
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
  : Tot(i:(seq_index s){ fm.f s i /\ filter_map_map fm s i = j })
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
  (i: seq_index s {fm.f s i})
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
  (s: seq a {length s > 0 /\ fm.f s (length s - 1)})
  : Lemma (ensures (let fms = filter_map fm s in
                    let fms' = filter_map fm (hprefix s) in
                    let me = fm.m s (length s - 1) in
                    fms == append1 fms' me))
  = ()

let lemma_filter_map_extend_unsat
  (#a:_)
  (#b:eqtype)
  (fm: fm_t a b)
  (s: seq a {length s > 0 /\ not (fm.f s (length s - 1))})
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

let pred_idxfn (#p:nat{p > 0}) (#a:_) (#b:_) (f:sidxfn_t p a b)
  : sidxfn_t (p-1) a b
  = f

let pred_cond_idxfn (#p:nat{p>0}) (#a:_) (#b:_) (#f:sidxfn_t p a bool) (m:scond_idxfn_t b f)
  : scond_idxfn_t b (pred_idxfn f)
  = m

let pred (#p:_{p > 0}) (#a:_) (#b: _)  (fm: ssfm_t p a b)
  : ssfm_t (p-1) a b
  = SSFM (pred_idxfn fm.f) (pred_cond_idxfn fm.m)

let rec ssfilter_map (#p:_) (#a #b:_)
  (fm: ssfm_t p a b)
  (s: sseq a{length s = p})
  : Tot(s':sseq b {length s' = length s})
    (decreases (length s))
  = let n = length s in
    if n = 0 then empty #(seq b)
    else
      let fmss' = ssfilter_map (pred fm) (prefix s (n-1)) in
      let fmi = to_fm_t fm (n - 1) in
      let fms = filter_map fmi (index s (n-1)) in
      append1 fmss' fms

let rec ssfilter_map_map (#p:_) (#a #b:_)
  (fm: ssfm_t p a b)
  (s: sseq a {length s = p})
  (ii: sseq_index s {ssfn fm.f s ii})
  : Tot(jj: (sseq_index (ssfilter_map fm s))
    {indexss (ssfilter_map fm s) jj == cond_ssfn fm.m s ii /\
     fst ii = fst jj})
    (decreases (length s))
  = let t,i = ii in
    let n = length s in
    if t = n - 1 then
      let fmi = to_fm_t fm (n - 1) in
      t, filter_map_map fmi (index s (n-1)) i
    else
      ssfilter_map_map (pred fm) (prefix s (n-1)) ii

let rec ssfilter_map_invmap (#p:_) (#a #b:_)
  (fm: ssfm_t p a b)
  (s: sseq a {length s = p})
  (jj: sseq_index (ssfilter_map fm s))
  : Tot(ii:(sseq_index s){ssfn fm.f s ii /\ ssfilter_map_map fm s ii = jj })
    (decreases (length s))
  = let t,j = jj in
    let n = length s in
    if t = n - 1 then
      let fmi = to_fm_t fm (n - 1) in
      t, filter_map_invmap fmi (index s (n - 1)) j
    else
      ssfilter_map_invmap (pred fm) (prefix s (n - 1)) jj

let rec lemma_ssfilter_map (#p:_) (#a #b:_)
  (fm: ssfm_t p a b)
  (s: sseq a{length s = p})
  (ii: sseq_index s {ssfn fm.f s ii})
  : Lemma (ensures (let jj = ssfilter_map_map fm s ii in
                    ii = ssfilter_map_invmap fm s jj))
          (decreases (length s))
  = let t,i = ii in
    let n = length s in
    if t = n - 1 then ()
    else
      lemma_ssfilter_map (pred fm) (prefix s (n-1)) ii

let rec lemma_ssfilter_map_idx (#p:_) (#a #b:_)
  (ssfm: ssfm_t p a b)
  (ss: sseq a{length ss = p})
  (i: seq_index ss)
  : Lemma (ensures (index (ssfilter_map ssfm ss) i = filter_map (to_fm_t ssfm i) (index ss i)))
          (decreases (length ss))
  = let n = length ss in
    if i = n - 1 then ()
    else
      lemma_ssfilter_map_idx (pred ssfm) (prefix ss (n - 1)) i
