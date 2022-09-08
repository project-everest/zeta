module Zeta.IdxFn

let conj_is_idxfn (#gs:_) (f1 f2: idxfn_t gs bool)
  : Lemma (ensures (prefix_property (conj f1 f2)))
  = ()

(* length of applying a filter to *)
let rec flen (#gs:_) (f: idxfn_t gs bool) (s: seq_t gs)
  : Tot (l:nat{ l <=  Seq.length s})
    (decreases Seq.length s)
  = let n = Seq.length s in
    if n = 0 then 0
    else
      let s' = prefix s (n - 1) in
      let l' = flen f s' in
      if f s (n - 1) then 1 + l'
      else l'

(* map every index satisfying the filter to the index in the filtered sequence *)
let rec idx2fidx (#gs:_) (f: idxfn_t gs bool) (s: seq_t gs) (i: seq_index s{f s i})
  : Tot (j:nat {j < flen f s})
    (decreases Seq.length s)
  = let n = Seq.length s - 1 in
    let s' = prefix s n in
    if i = n then flen f s'
    else idx2fidx f s' i

let rec fidx2idx (#gs:_) (f: idxfn_t gs bool) (s: seq_t gs) (j: nat {j < flen f s})
  : Tot (i:seq_index s{f s i /\ idx2fidx f s i = j})
    (decreases Seq.length s)
  = let n = Seq.length s - 1 in
    let s' = prefix s n in
    let l' = flen f s' in
    if j = l' then n
    else fidx2idx f s' j

let rec lemma_idx2fidx (#gs:_) (f: idxfn_t gs bool) (s: seq_t gs) (i: seq_index s{f s i })
  : Lemma (ensures (i = fidx2idx f s (idx2fidx f s i)))
        (decreases Seq.length s)
  = let n = Seq.length s - 1 in
    let s' = prefix s n in
    if i = n then ()
    else lemma_idx2fidx f s' i

let rec idx2fidx_prefix_property (#gs:_)
  (f: idxfn_t gs bool)
  (s: seq_t gs)
  (i: seq_index s {f s i})
  (j: nat{j <= Seq.length s /\ j > i})
  : Lemma (ensures (idx2fidx f s i = idx2fidx f (prefix s j) i))
          (decreases Seq.length s)
  = let n = Seq.length s - 1 in
    let s' = prefix s n in
    if i = n then ()
    else if j = n + 1 then ()
    else idx2fidx_prefix_property f s' i j

let rec idx2fidx_monotonic_aux (#gs:_)
  (f: idxfn_t gs bool)
  (s: seq_t gs)
  (i1 i2: (i:seq_index s {f s i}))
  : Lemma (ensures (i1 < i2 ==> idx2fidx f s i1 < idx2fidx f s i2))
          (decreases Seq.length s)
  = let n = Seq.length s - 1 in
    let s' = prefix s n in
    if i1 >= i2 then ()
    else if i2 = n then ()
    else
      idx2fidx_monotonic_aux f s' i1 i2

let idx2fidx_monotonic (#gs:_)
  (f: idxfn_t gs bool)
  (s: seq_t gs)
  (i1 i2: (i:seq_index s {f s i}))
  : Lemma (ensures ((i1 < i2 ==> idx2fidx f s i1 < idx2fidx f s i2) /\
                    (i2 < i1 ==> idx2fidx f s i1 > idx2fidx f s i2)))
  = idx2fidx_monotonic_aux f s i1 i2;
    idx2fidx_monotonic_aux f s i2 i1

let fidx2idx_monotonic (#gs:_)
  (f: idxfn_t gs bool)
  (s: seq_t gs)
  (i1 i2: (i:nat{i < flen f s}))
  : Lemma (ensures ((i1 < i2 ==> fidx2idx f s i1 < fidx2idx f s i2) /\
                    (i2 < i1 ==> fidx2idx f s i1 > fidx2idx f s i2)))
  = idx2fidx_monotonic f s (fidx2idx f s i1) (fidx2idx f s i2)

let lemma_fextend_snoc (#gs:_) (f: idxfn_t gs bool) (s: seq_t gs {Seq.length s > 0})
  : Lemma (ensures (let i = Seq.length s - 1 in
                    let s' = prefix s i in
                    if f s i then
                      flen f s = flen f s' + 1 /\
                      idx2fidx f s i  = flen f s' /\
                      fidx2idx f s (flen f s') = i
                    else
                      flen f s = flen f s'))
  = ()

let rec lemma_idx2fidx_idem (#gs:_) (f: idxfn_t gs bool) (s: seq_t gs{flen f s = Seq.length s}) (i: seq_index s)
  : Lemma (ensures (f s i /\ idx2fidx f s i = i))
          (decreases (Seq.length s))
  = let j = Seq.length s - 1 in
    let s' = prefix s j in
    if i <> j then
      lemma_idx2fidx_idem f s' i

let lemma_filter_map_extend_sat
  (#gs:_)
  (#b:_)
  (fm: fm_t gs b)
  (s: seq_t gs {Seq.length s > 0 /\ fm.f s (Seq.length s - 1)})
  : Lemma (ensures (let fms = filter_map fm s in
                    let fms' = filter_map fm (prefix s (Seq.length s - 1)) in
                    let me = fm.m s (Seq.length s - 1) in
                    fms == SA.append1 fms' me))
  = let n = Seq.length s in
    let s' = prefix s (n - 1) in
    let fms = filter_map fm s in
    let fms' = filter_map fm s' in
    let me = fm.m s (n - 1) in
    let fmsc = SA.append1 fms' me in
    assert(length fms = length fmsc);

    let aux (i: SA.seq_index fms)
      : Lemma (ensures (index fms i == index fmsc i))
              [SMTPat (index fms i == index fmsc i)]
      = ()
    in
    assert(equal fms fmsc);
    ()

let lemma_filter_map_extend_unsat
  (#gs:_)
  (#b:_)
  (fm: fm_t gs b)
  (s: seq_t gs {Seq.length s > 0 /\ not (fm.f s (Seq.length s - 1))})
  : Lemma (ensures (let fms = filter_map fm s in
                    let fms' = filter_map fm (prefix s (Seq.length s - 1)) in
                    fms == fms'))
  = let n = Seq.length s in
    let s' = prefix s (n - 1) in
    let fms = filter_map fm s in
    let fms' = filter_map fm s' in
    let aux (i: SA.seq_index fms)
      : Lemma (ensures (index fms i == index fms' i))
              [SMTPat (index fms i == index fms' i)]
      = ()
    in
    assert(equal fms fms');
    ()

let lemma_filter_map_snoc
  (#gs:_)
  (#b:_)
  (fm: fm_t gs b)
  (s: seq_t gs {Seq.length s > 0})
  : Lemma (ensures (let fms = filter_map fm s in
                    let i = Seq.length s - 1 in
                    let fms' = filter_map fm (prefix s i) in
                    if fm.f s i then
                      let me = fm.m s i in
                      fms == SA.append1 fms' me
                    else
                      fms == fms'))
  = let i = Seq.length s - 1 in
    let s' = prefix s i in
    let fms = filter_map fm s in
    let fms' = filter_map fm s' in
    if fm.f s i then
      lemma_filter_map_extend_sat fm s
    else
      lemma_filter_map_extend_unsat fm s

module S = FStar.Seq

let lemma_filter_map_prefix_len
  (#gs:_)
  (#b:eqtype)
  (fm: fm_t gs b)
  (s: seq_t gs)
  (l: nat{l <= Seq.length s})
  : Lemma (ensures (let fms = filter_map fm s in
                    let s' = prefix s l in
                    let fms' = filter_map fm s' in
                    S.length fms >= S.length fms'))
  = let fms = filter_map fm s in
    let s' = prefix s l in
    let fms' = filter_map fm s' in

    if S.length fms < S.length fms' then
      let j = S.length fms' - 1 in
      let i = filter_map_invmap fm s' j in
      filter_map_map_prefix_property fm s i l

let lemma_filter_map_prefix
  (#gs:_)
  (#b:eqtype)
  (fm: fm_t gs b)
  (s: seq_t gs)
  (l: nat{l <= Seq.length s})
  : Lemma (ensures (let fms = filter_map fm s in
                    let s' = prefix s l in
                    let fms' = filter_map fm s' in
                    fms' `prefix_of` fms))
  = let fms = filter_map fm s in
    let s' = prefix s l in
    let fms' = filter_map fm s' in
    lemma_filter_map_prefix_len fm s l;
    assert(S.length fms' <= S.length fms);
    let fms'' = SA.prefix fms (S.length fms') in
    assert(S.length fms'' = S.length fms');
    let aux(j:_)
      : Lemma (ensures (S.index fms' j = S.index fms'' j))
      = let i = filter_map_invmap fm s' j in
        filter_map_map_prefix_property fm s i l
    in
    FStar.Classical.forall_intro aux;
    assert(equal fms'' fms')

let rec lemma_monotonic_filter_aux (#gs:_)
  (f: idxfn_t gs bool{monotonic f})
  (s: seq_t gs {Seq.length s > 0 /\ f s (Seq.length s - 1)})
  : Lemma (ensures (flen f s = Seq.length s))
          (decreases Seq.length s)
  = let n = Seq.length s in
    if n = 1 then admit ()
    else begin
      let s' = prefix s (n - 1) in
      lemma_monotonic_filter_aux f s'
    end

let lemma_monotonic_filter (#gs:_)
  (f: idxfn_t gs bool{monotonic f})
  (s: seq_t gs)
  (i: seq_index s{f s i})
  : Lemma (ensures (idx2fidx f s i = i))
  = let n = Seq.length s in
    idx2fidx_prefix_property f s i (i+1);
    let s' = prefix s (i+1) in
    lemma_monotonic_filter_aux f s'

let lemma_alltrue_len (#gs:gen_seq_spec)
  (s: seq_t gs)
  : Lemma (ensures (flen (all_true gs) s = Seq.length s))
          [SMTPat (flen (all_true gs) s)]
  = if Seq.length s = 0 then ()
    else
      lemma_monotonic_filter_aux (all_true gs) s

let lemma_map_length (#gs:_) (#b:_) (m: idxfn_t gs b) (s: seq_t gs)
  : Lemma (ensures (length (map m s) = Seq.length s))
  = ()

let lemma_map_map
  (#gs:_)
  (#b:_)
  (m: idxfn_t gs b)
  (s: seq_t gs)
  (i: seq_index s)
  : Lemma (ensures (let fm = map_fm m in
                    filter_map_map fm s i = i))
  = ()


let fm_is_map (#gs_a #gs_b:gen_seq_spec) (#c:_)
  (f:gs_a.a -> gs_b.a)
  (fm:fm_t gs_a c)
  (fm_map:fm_t gs_b c)
  = (forall (s:Seq.seq gs_a.a). gs_a.phi s <==> gs_b.phi (SA.map f s)) /\  
    (forall (s:seq_t gs_a) (i:seq_index s). fm.f s i == fm_map.f (SA.map f s) i) /\
    (forall (s:seq_t gs_a) (i:seq_index s{fm.f s i}). fm.m s i == fm_map.m (SA.map f s) i)

let prefix_map (#a #b:_) (s:Seq.seq a) (i:nat{i <= Seq.length s})
  (f:a -> b)
  : Lemma (SA.map f (SA.prefix s i) == SA.prefix (SA.map f s) i)
          [SMTPat (SA.prefix (SA.map f s) i)]
  = assert (Seq.equal (SA.map f (SA.prefix s i))
                      (SA.prefix (SA.map f s) i))

let rec flen_fm_map (#gs_a #gs_b:gen_seq_spec) (#c:_)
  (f:gs_a.a -> gs_b.a)
  (fm:fm_t gs_a c)
  (fm_map:fm_t gs_b c{fm_is_map f fm fm_map})
  (s:seq_t gs_a)
  : Lemma (ensures flen fm.f s == flen fm_map.f (SA.map f s))
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else flen_fm_map f fm fm_map (prefix s (Seq.length s - 1))

let rec fidx2idx_fm_map (#gs_a #gs_b:gen_seq_spec) (#c:_)
  (f:gs_a.a -> gs_b.a)
  (fm:fm_t gs_a c)
  (fm_map:fm_t gs_b c{fm_is_map f fm fm_map})
  (s:seq_t gs_a)
  (j:nat{j < flen fm.f s})
  : Lemma
    (ensures flen fm.f s == flen fm_map.f (SA.map f s) /\
             fidx2idx fm.f s j == fidx2idx fm_map.f (SA.map f s) j)
    (decreases Seq.length s)
  = flen_fm_map f fm fm_map s;
    if Seq.length s = 0 then ()
    else begin
      let pfx = prefix s (Seq.length s - 1) in
      if j = flen fm.f pfx then ()
      else fidx2idx_fm_map f fm fm_map pfx j
    end

let filter_map_maps (#gs_a #gs_b:gen_seq_spec) (#c:_)
  (f:gs_a.a -> gs_b.a)
  (fm:fm_t gs_a c)
  (fm_map:fm_t gs_b c{fm_is_map f fm fm_map})
  (s:seq_t gs_a)
  : Lemma (filter_map fm s == filter_map fm_map (SA.map f s))
  = flen_fm_map f fm fm_map s;
    let aux (j:nat{j < flen fm.f s})
      : Lemma (Seq.index (filter_map fm s) j ==
               Seq.index (filter_map fm_map (SA.map f s)) j)
              [SMTPat ()]
      = fidx2idx_fm_map f fm fm_map s j
    in
    assert (Seq.equal (filter_map fm s) (filter_map fm_map (SA.map f s)))
