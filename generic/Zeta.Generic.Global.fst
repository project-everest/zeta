module Zeta.Generic.Global

let lemma_prefix_verifiable #vspec (gl: verifiable_log vspec) (i:nat{i <= S.length gl})
  : Lemma (ensures (verifiable (SA.prefix gl i)))
          [SMTPat (SA.prefix gl i)]
  = admit()

let rec filter_map (#vspec:_) (#b:_)
  (fm: fm_t vspec b)
  (gl: verifiable_log vspec)
  : Tot (s:sseq b {S.length s = S.length gl})
    (decreases (S.length gl))
  = let n = S.length gl in
    if n = 0 then empty #(seq b)
    else
      let gl' = SA.prefix gl (n - 1) in
      let tl = thread_log gl (n - 1) in
      let fmss' = filter_map fm (SA.prefix gl (n-1)) in
      let fms = T.filter_map fm tl in
      append1 fmss' fms

let rec filter_map_map (#vspec:_) (#b:_)
  (fm: fm_t vspec b)
  (gl: verifiable_log vspec)
  (ii: sseq_index gl {idxfn fm.f gl ii})
  : Tot(jj: (sseq_index (filter_map fm gl))
    {indexss (filter_map fm gl) jj == cond_idxfn fm.m gl ii /\
     fst ii = fst jj})
    (decreases (S.length gl))
  = let t,i = ii in
    let n = S.length gl in
    if t = n - 1 then
      t, T.filter_map_map fm (thread_log gl (n-1)) i
    else
      filter_map_map fm (SA.prefix gl (n-1)) ii

let rec filter_map_invmap (#vspec:_) (#b:_)
  (fm: fm_t vspec b)
  (gl: verifiable_log vspec)
  (jj: sseq_index (filter_map fm gl))
  : Tot(ii:(sseq_index gl){idxfn fm.f gl ii /\ filter_map_map fm gl ii = jj })
    (decreases (S.length gl))
  = let t,j = jj in
    let n = S.length gl in
    if t = n - 1 then
      t, T.filter_map_invmap fm (thread_log gl (n - 1)) j
    else
      filter_map_invmap fm (SA.prefix gl (n - 1)) jj

let rec lemma_filter_map (#vspec:_)  (#b:_)
  (fm: fm_t vspec b)
  (gl: verifiable_log vspec)
  (ii: sseq_index gl {idxfn fm.f gl ii})
  : Lemma (ensures (let jj = filter_map_map fm gl ii in
                    ii = filter_map_invmap fm gl jj))
          (decreases (S.length gl))
  = let t,i = ii in
    let n = S.length gl in
    if t = n - 1 then ()
    else
      lemma_filter_map fm (SA.prefix gl (n-1)) ii

let rec lemma_filter_map_idx (#vspec:_) (#b:_)
  (fm: fm_t vspec b)
  (gl: verifiable_log vspec)
  (i: SA.seq_index gl)
  : Lemma (ensures (S.index (filter_map fm gl) i = T.filter_map fm (thread_log gl i)))
          (decreases (S.length gl))
  = let n = S.length gl in
    if i = n - 1 then ()
    else
      lemma_filter_map_idx fm (SA.prefix gl (n - 1)) i
