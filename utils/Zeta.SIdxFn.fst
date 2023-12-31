module Zeta.SIdxFn

module IF = Zeta.IdxFn

let apply (#b:_) (gs:gen_sseq) (fm: fm_t gs.gsi b) (s: seq_t gs.gso) (i:nat{i < Seq.length s})
  = IF.filter_map fm (gs.index s i)

let filter_map (#b:_) (gs:gen_sseq)
  (fm: fm_t gs.gsi b)
  (ss: seq_t gs.gso)
  : Tot(ss':sseq b {S.length ss' = Seq.length ss})
  = IF.map (apply gs fm) ss

let filter_map_map (#b:_) (gs:gen_sseq)
  (fm: fm_t gs.gsi b)
  (ss: seq_t gs.gso)
  (ii: sseq_index ss {idxfn gs fm.f ss ii})
  : jj: (SS.sseq_index (filter_map gs fm ss))
    {indexss (filter_map gs fm ss) jj == cond_idxfn fm.m ss ii /\
     fst ii = fst jj}
  = let mfm = map_fm (apply gs fm) in
    let t,i = ii in
    let i' = IF.filter_map_map fm (gs.index ss t) i in
    lemma_map_map (apply gs fm) ss t;
    (t,i')

let filter_map_invmap (#b:_) (gs:gen_sseq)
  (fm: fm_t gs.gsi b)
  (ss: seq_t gs.gso)
  (jj: SS.sseq_index (filter_map gs fm ss))
  : ii:(sseq_index ss){idxfn gs fm.f ss ii /\ filter_map_map gs fm ss ii = jj }
  = let mfm = map_fm (apply gs fm) in
    let t,j = jj in
    lemma_map_map (apply gs fm) ss t;
    let i = IF.filter_map_invmap fm (gs.index ss t) j in
    (t,i)

let lemma_filter_map (#b:_) (gs:gen_sseq)
  (fm: fm_t gs.gsi b)
  (ss: seq_t gs.gso)
  (ii: sseq_index ss {idxfn gs fm.f ss ii})
  : Lemma (ensures (let jj = filter_map_map gs fm ss ii in
                    ii = filter_map_invmap gs fm ss jj))
  = let mfm = map_fm (apply gs fm) in
    let t,_ = ii in
    lemma_map_map (apply gs fm) ss t

let lemma_filter_map_idx (#b:_) (gs:gen_sseq)
  (fm: fm_t gs.gsi b)
  (s: seq_t gs.gso)
  (i: nat{i < Seq.length s})
  : Lemma (ensures (S.index (filter_map gs fm s) i == Zeta.IdxFn.filter_map fm (gs.index s i)))
  = lemma_map_map (apply gs fm) s i
