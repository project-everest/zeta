module Zeta.IdxFn

open FStar.FunctionalExtensionality
open FStar.Seq
open Zeta.SeqAux

let idx (n:nat) = i:nat{i < n}

let pfx (n:nat) = i:nat{i <= n}

let idxfn_t (n:nat) (b:_) = idx n -> b

let restrict_idxfn (#n #b:_) (f: idxfn_t n b) (m:pfx n)
  : idxfn_t m b
  = f

let cond_idxfn_t (#n:nat) (b:_) (f:idxfn_t n bool) = i:idx n{f i} -> b

let restrict_cond_idxfn (#n:nat) (#b #p:_) (f: cond_idxfn_t b p) (m:nat{m <= n})
  : cond_idxfn_t b (restrict_idxfn #n p m)
  = f

val flen_base (#n:_) (f: idxfn_t n bool)
  : l':nat{l' < n}

val flen_feq (#n:_) (f1 f2: idxfn_t n bool)
  : Lemma (ensures (feq f1 f2 ==> flen_base f1 = flen_base f2))
          [SMTPat (feq f1 f2)]

(* length of applying a filter to *)
let flen (#n:_) (f: idxfn_t n bool) (l:pfx n)
  : l':nat{ l' < l }
  = flen_base (restrict_idxfn f l)

(* map every index satisfying the filter to the index in the filtered sequence *)
val idx2fidx_base (#n:_) (f: idxfn_t n bool) (i:idx n{f i})
  : j:nat {j < flen f n}

val idx2fidx_feq (#n:_) (f1 f2: idxfn_t n bool) (i: idx n{f1 i})
  : Lemma (ensures (feq f1 f2 ==> idx2fidx_base f1 i = idx2fidx_base f2 i))

let idx2fidx (#n:_) (f: idxfn_t n bool) (l:pfx n) (i:idx l{f i})
  : j:nat {j < flen f l}
  = let f' = restrict_idxfn f l in
    idx2fidx_base f' i

val fidx2idx_base (#n:_) (f: idxfn_t n bool) (j: idx (flen f n))
  : i:idx n{f i /\ idx2fidx f n i = j}

let fidx2idx (#n:_) (f: idxfn_t n bool) (l:pfx n) (j: idx (flen f l))
  : i:idx l{f i /\ idx2fidx f l i = j}
  = let f' = restrict_idxfn f l in
    fidx2idx_base f' j

val lemma_idx2fidx (#n:_) (f: idxfn_t n bool) (l:pfx n) (i: idx l{f i })
  : Lemma (ensures (i = fidx2idx f l (idx2fidx f l i)))
          [SMTPat (idx2fidx f l i)]

val idx2fidx_prefix_property (#n:_)
  (f: idxfn_t n bool)
  (l: pfx n)
  (l': pfx l)
  (i: idx l' {f i})
  : Lemma (ensures (idx2fidx f l i = idx2fidx f l' i))

val idx2fidx_monotonic (#n:_)
  (f: idxfn_t n bool)
  (l: pfx n)
  (i1 i2: (i:idx l {f i}))
  : Lemma (ensures ((i1 < i2 ==> idx2fidx f l i1 < idx2fidx f l i2) /\
                    (i2 < i1 ==> idx2fidx f l i1 > idx2fidx f l i2)))

val fidx2idx_monotonic (#n:_)
  (f: idxfn_t n bool)
  (l: pfx n)
  (i1 i2: idx (flen f l))
  : Lemma (ensures ((i1 < i2 ==> fidx2idx f l i1 < fidx2idx f l i2) /\
                    (i2 < i1 ==> fidx2idx f l i1 > fidx2idx f l i2)))

val lemma_fempty (#n:_) (f: idxfn_t n bool)
  : Lemma (ensures (flen f 0 = 0))

val lemma_fsnoc (#n:_) (f: idxfn_t n bool) (l: pfx n{l > 0})
  : Lemma (ensures (if f (l - 1) then
                      flen f l = flen f (l - 1) + 1 /\
                      idx2fidx f l (l - 1) = flen f (l - 1) /\
                      fidx2idx f l (flen f (l - 1)) = l - 1
                    else
                      flen f l = flen f (l - 1)))

(* a specification of a filter-map *)
noeq
type fm_t (n:_) (b:_) =
  | FM: f: idxfn_t n bool   ->
        m: cond_idxfn_t b f -> fm_t n b

let to_fm (#n:_) (#b:_) (f:idxfn_t n bool) (m: cond_idxfn_t b f)
  : fm_t n b
  = FM f m

let filter_map_base (#n #b:_)
  (fm: fm_t n b)
  : s:seq b {length s = flen fm.f n}
  = init (flen fm.f n) (fun j -> fm.m (fidx2idx fm.f n j))

let filter_map (#n #b:_)
  (fm: fm_t n b)
  (l: pfx n)
  : s: seq b {length s = flen fm.f l}
  = let f' = restrict_idxfn fm.f l in
    let m' = restrict_cond_idxfn fm.m l in
    let fm' = to_fm f' m' in
    filter_map_base fm'

(* map an index of the original sequence to the filter-mapped sequence *)
let filter_map_map (#n #b:_)
  (fm: fm_t n b)
  (l: pfx n)
  (i: idx l {fm.f i})
  : j: (seq_index (filter_map fm l)) {index (filter_map fm l) j == fm.m i /\
                                      j = idx2fidx fm.f l i}
  = idx2fidx fm.f l i

let filter_map_map_prefix_property (#n #b:_)
  (fm: fm_t n b)
  (l: pfx n)
  (l': pfx l)
  (i: idx l' {fm.f i})
  : Lemma (ensures (filter_map_map fm l i = filter_map_map fm l' i))
  = idx2fidx_prefix_property fm.f l l' i

let lemma_filter_map_map_monotonic (#n #b:_)
  (fm: fm_t n b)
  (l: pfx n)
  (i1 i2: (i:(idx l) {fm.f i}))
  : Lemma (ensures ((i1 < i2 ==> filter_map_map fm l i1 < filter_map_map fm l i2) /\
                    (i1 > i2 ==> filter_map_map fm l i1 > filter_map_map fm l i2)))
  = idx2fidx_monotonic fm.f l i1 i2

(* map an index of the filter-map back to the original sequence *)
let filter_map_invmap (#n #b:_)
  (fm: fm_t n b)
  (l: pfx n)
  (j: seq_index (filter_map fm l))
  : i:idx l{fm.f i /\ filter_map_map fm l i = j /\ i = fidx2idx fm.f l j }
  = fidx2idx fm.f l j

let filter_map_invmap_monotonic (#n #b:_)
  (fm: fm_t n b)
  (l: pfx n)
  (j1 j2: seq_index (filter_map fm l))
  : Lemma (ensures (j1 < j2 ==> filter_map_invmap fm l j1 < filter_map_invmap fm l j2) /\
                   (j1 > j2 ==> filter_map_invmap fm l j1 > filter_map_invmap fm l j2))
  = fidx2idx_monotonic fm.f l j1 j2

val lemma_filter_map_empty
  (#n:_)
  (#b:_)
  (fm: fm_t n b)
  : Lemma (ensures filter_map fm 0 == empty #b)

val lemma_filter_map_snoc
  (#n:_)
  (#b:_)
  (fm: fm_t n b)
  (l: pfx n {l > 0})
  : Lemma (ensures (let s = filter_map fm l in
                    let s' = filter_map fm (l-1) in
                    if fm.f (l - 1) then
                      s == append1 s' (fm.m (l - 1))
                    else
                      s == s'))

let monotonic (#n:_) (f: idxfn_t n bool)
  = forall (i1 i2: idx n).
        i1 < i2 ==>
        f i2 ==>
        f i1

(* return true everywhere; assert(monotonic (all_true gs))*)
let all_true (n:nat) (i:idx n)
  = true

val lemma_monotonic_filter (#n:_)
  (f: idxfn_t n bool{monotonic f})
  (l: pfx n)
  (i: idx l{f i})
  : Lemma (ensures (idx2fidx f l i = i))
          [SMTPat (idx2fidx f l i)]

let map_fm (#n:_) (#b:_) (m: idxfn_t n b)
  : fm_t n b
  = FM (all_true n) m

let map (#n:_) (#b:_) (m: idxfn_t n b) (l:pfx n)
  : seq b
  = let fm = map_fm m in
    filter_map fm l

val lemma_map_length (#n:_) (#b:_) (m: idxfn_t n b) (l: pfx n)
  : Lemma (ensures (length (map m l) = l))
          [SMTPat (map m l)]

val lemma_map_map
  (#n:_)
  (#b:_)
  (m: idxfn_t n b)
  (l: pfx n)
  (i: idx l)
  : Lemma (ensures (let fm = map_fm m in
                    filter_map_map fm l i = i))

(* conjunction of two index filters *)
let conj #n (f1 f2: idxfn_t n bool)
  = fun (i: idx n) -> f1 i && f2 i

val lemma_filter_map_monotonic
  (#n:_)
  (b:_)
  (f:idxfn_t n bool{monotonic f})
  (fm: fm_t n b)
  (l: pfx n)
  : Lemma (ensures (filter_map (FM (conj fm.f f) fm.m) l == filter_map fm (flen f l)))

val lemma_map_prefix
  (#n:_)
  (#b:_)
  (f: idxfn_t n b)
  (l: pfx n)
  (l': pfx l)
  : Lemma (ensures (prefix (map f l) l' == map f l'))

let indexf_base (#a #b:eqtype) (f: a -> b) (s: seq a) (i: seq_index s)
  : b
  = f (index s i)

let indexf (#a #b:eqtype) (f: a -> b) (s: seq a)
  : idxfn_t (length s) b
  = indexf_base f s

let indexm_base (#a #b:eqtype) (f: a -> bool) (m: (x:a{f x}) -> b) (s: seq a) (i:seq_index s{f (index s i)})
  : b
  = m (index s i)

let indexm (#a #b:eqtype) (f: a -> bool) (m: (x:a{f x}) -> b) (s: seq a)
  : cond_idxfn_t #(length s) b (indexf f s)
  = indexm_base f m s

let simple_fm (#a #b: eqtype) (f: a->bool) (m: (x:a{f x}) -> b) (s: seq a)
  : fm_t (length s) b
  = FM (indexf f s) (indexm f m s)

let simple_filter_map (#a #b:eqtype) (f: a -> bool) (m: (x:a{f x}) -> b) (s: seq a)
  : seq b
  = let fm = simple_fm f m s in
    filter_map fm (length s)

let lemma_simple_filter_map_empty (#a #b: eqtype) (f: a -> bool) (m: (x:a{f x}) -> b) (s: seq a{length s = 0})
  : Lemma (ensures (simple_filter_map f m s == empty #b))
  = ()

let lemma_simple_filter_map_snoc(#a #b: eqtype) (f: a -> bool) (m: (x:a{f x}) -> b) (s: seq a{length s > 0})
  : Lemma (ensures (let i = length s - 1 in
                    let s' = prefix s i in
                    let fms = simple_filter_map f m s in
                    let fms' = simple_filter_map f m s' in
                    if f (index s i) then
                      fms == append1 fms' (m (index s i))
                    else
                      fms == fms'))
  = let i = length s - 1 in
    let s' = prefix s i in
    let fi = indexf f s in
    let fi' = indexf f s' in
    assert(feq (restrict_idxfn fi i) fi');
    //assert(restrict_idxfn fi i == fi');
    let mi = indexm f m s in
    let mi' = indexm f m s' in
    //assume(restrict_cond_idxfn mi i == mi');
    let fm = simple_fm f m s in
    lemma_filter_map_snoc fm (i+1);
    admit()

let seqfn_t (n:nat) (b:_)
  = l:pfx n -> b

let to_pre_fn (#n #b:_) (f: seqfn_t n b) (l:pfx n) (i:idx l)
  : b
  = f i

let to_post_fn (#n #b:_) (f: seqfn_t n b) (l:pfx n) (i:idx l)
  : b
  = f (i + 1)

let simple_map_fm (#a #b: eqtype) (m: a -> b) (s: seq a)
  : fm_t (length s) b
  = FM (all_true (length s)) (indexf m s)

let simple_map (#a #b: eqtype) (m: a -> b) (s: seq a)
  : seq b
  = let fm = simple_map_fm m s in
    filter_map fm (length s)
