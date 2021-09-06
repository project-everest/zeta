module Zeta.IdxFn

let conj_is_idxfn (#gs:_) (f1 f2: idxfn_t gs bool)
  : Lemma (ensures (prefix_property (conj f1 f2)))
  = ()

(* length of applying a filter to *)
let rec flen (#gs:_) (f: idxfn_t gs bool) (s: gs.seq_t)
  : Tot (l:nat{ l <=  gs.length s})
    (decreases gs.length s)
  = let n = gs.length s in
    if n = 0 then 0
    else
      let s' = gs.prefix s (n - 1) in
      let l' = flen f s' in
      if f s (n - 1) then 1 + l'
      else l'

(* map every index satisfying the filter to the index in the filtered sequence *)
let rec idx2fidx (#gs:_) (f: idxfn_t gs bool) (s: gs.seq_t) (i: seq_index s{f s i})
  : Tot (j:nat {j < flen f s})
    (decreases gs.length s)
  = let n = gs.length s - 1 in
    let s' = gs.prefix s n in
    if i = n then flen f s'
    else idx2fidx f s' i

let rec fidx2idx (#gs:_) (f: idxfn_t gs bool) (s: gs.seq_t) (j: nat {j < flen f s})
  : Tot (i:seq_index s{f s i /\ idx2fidx f s i = j})
    (decreases gs.length s)
  = let n = gs.length s - 1 in
    let s' = gs.prefix s n in
    let l' = flen f s' in
    if j = l' then n
    else fidx2idx f s' j

let rec lemma_idx2fidx (#gs:_) (f: idxfn_t gs bool) (s: gs.seq_t) (i: seq_index s{f s i })
  : Lemma (ensures (i = fidx2idx f s (idx2fidx f s i)))
        (decreases gs.length s)
  = let n = gs.length s - 1 in
    let s' = gs.prefix s n in
    if i = n then ()
    else lemma_idx2fidx f s' i

let rec idx2fidx_prefix_property (#gs:_)
  (f: idxfn_t gs bool)
  (s: gs.seq_t)
  (i: seq_index s {f s i})
  (j: nat{j <= gs.length s /\ j > i})
  : Lemma (ensures (idx2fidx f s i = idx2fidx f (gs.prefix s j) i))
          (decreases gs.length s)
  = let n = gs.length s - 1 in
    let s' = gs.prefix s n in
    if i = n then ()
    else if j = n + 1 then ()
    else idx2fidx_prefix_property f s' i j

let rec idx2fidx_monotonic_aux (#gs:_)
  (f: idxfn_t gs bool)
  (s: gs.seq_t)
  (i1 i2: (i:seq_index s {f s i}))
  : Lemma (ensures (i1 < i2 ==> idx2fidx f s i1 < idx2fidx f s i2))
          (decreases gs.length s)
  = let n = gs.length s - 1 in
    let s' = gs.prefix s n in
    if i1 >= i2 then ()
    else if i2 = n then ()
    else
      idx2fidx_monotonic_aux f s' i1 i2

let idx2fidx_monotonic (#gs:_)
  (f: idxfn_t gs bool)
  (s: gs.seq_t)
  (i1 i2: (i:seq_index s {f s i}))
  : Lemma (ensures ((i1 < i2 ==> idx2fidx f s i1 < idx2fidx f s i2) /\
                    (i2 < i1 ==> idx2fidx f s i1 > idx2fidx f s i2)))
  = idx2fidx_monotonic_aux f s i1 i2;
    idx2fidx_monotonic_aux f s i2 i1

let fidx2idx_monotonic (#gs:_)
  (f: idxfn_t gs bool)
  (s: gs.seq_t)
  (i1 i2: (i:nat{i < flen f s}))
  : Lemma (ensures ((i1 < i2 ==> fidx2idx f s i1 < fidx2idx f s i2) /\
                    (i2 < i1 ==> fidx2idx f s i1 > fidx2idx f s i2)))
  = idx2fidx_monotonic f s (fidx2idx f s i1) (fidx2idx f s i2)

let lemma_fextend_sat (#gs:_) (f: idxfn_t gs bool) (s: gs.seq_t{gs.length s > 0})
  : Lemma (requires (f s (gs.length s - 1)))
          (ensures (let n = gs.length s in
                    let s' = gs.prefix s (n-1) in
                    flen f s = flen f s' + 1 /\
                    idx2fidx f s (n - 1) = flen f s' /\
                    fidx2idx f s (flen f s') = (n-1)))
  = ()

let lemma_fextend_unsat (#gs:_) (f: idxfn_t gs bool) (s: gs.seq_t{gs.length s > 0})
  : Lemma (requires (not (f s (gs.length s - 1))))
          (ensures (let n = gs.length s in
                    let s' = gs.prefix s (n-1) in
                    flen f s = flen f s'))
  = ()

let lemma_filter_map_extend_sat
  (#gs:_)
  (#b:_)
  (fm: fm_t gs b)
  (s: gs.seq_t {gs.length s > 0 /\ fm.f s (gs.length s - 1)})
  : Lemma (ensures (let fms = filter_map fm s in
                    let fms' = filter_map fm (gs.prefix s (gs.length s - 1)) in
                    let me = fm.m s (gs.length s - 1) in
                    fms == SA.append1 fms' me))
  = let n = gs.length s in
    let s' = gs.prefix s (n - 1) in
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
  (s: gs.seq_t {gs.length s > 0 /\ not (fm.f s (gs.length s - 1))})
  : Lemma (ensures (let fms = filter_map fm s in
                    let fms' = filter_map fm (gs.prefix s (gs.length s - 1)) in
                    fms == fms'))
  = let n = gs.length s in
    let s' = gs.prefix s (n - 1) in
    let fms = filter_map fm s in
    let fms' = filter_map fm s' in
    let aux (i: SA.seq_index fms)
      : Lemma (ensures (index fms i == index fms' i))
              [SMTPat (index fms i == index fms' i)]
      = ()
    in
    assert(equal fms fms');
    ()

let rec lemma_monotonic_filter_aux (#gs:_)
  (f: idxfn_t gs bool{monotonic f})
  (s: gs.seq_t {gs.length s > 0 /\ f s (gs.length s - 1)})
  : Lemma (ensures (flen f s = gs.length s))
          (decreases gs.length s)
  = let n = gs.length s in
    if n = 1 then ()
    else
      let s' = gs.prefix s (n - 1) in
      lemma_monotonic_filter_aux f s'

let lemma_monotonic_filter (#gs:_)
  (f: idxfn_t gs bool{monotonic f})
  (s: gs.seq_t)
  (i: seq_index s{f s i})
  : Lemma (ensures (idx2fidx f s i = i))
  = let n = gs.length s in
    idx2fidx_prefix_property f s i (i+1);
    let s' = gs.prefix s (i+1) in
    lemma_monotonic_filter_aux f s'

let lemma_alltrue_len (#gs:gen_seq_spec)
  (s: gs.seq_t)
  : Lemma (ensures (flen (all_true gs) s = gs.length s))
          [SMTPat (flen (all_true gs) s)]
  = if gs.length s = 0 then ()
    else
      lemma_monotonic_filter_aux (all_true gs) s

let lemma_map_length (#gs:_) (#b:_) (m: idxfn_t gs b) (s: gs.seq_t)
  : Lemma (ensures (length (map m s) = gs.length s))
  = ()

let lemma_map_map
  (#gs:_)
  (#b:_)
  (m: idxfn_t gs b)
  (s: gs.seq_t)
  (i: seq_index s)
  : Lemma (ensures (let fm = map_fm m in
                    filter_map_map fm s i = i))
  = ()

let lemma_filter_map_monotonic
  (#gs:_)
  (b:_)
  (f:idxfn_t gs bool{monotonic f})
  (fm: fm_t gs b)
  (s: gs.seq_t)
  : Lemma (ensures (filter_map (FM (conj fm.f f) fm.m) s == filter_map fm (gs.prefix s (flen f s))))
  = admit()
