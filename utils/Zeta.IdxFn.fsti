module Zeta.IdxFn

open FStar.Seq
open Zeta.SeqAux
module SA = Zeta.SeqAux

noeq
type gen_seq_base = {

  (* type of sequences of a *)
  seq_t: eqtype;

  (* return the length of the sequence *)
  length: seq_t -> nat;

  (* prefix function *)
  prefix: s: seq_t -> i: nat{i <= length s} -> s':seq_t {length s' = i}
}

let prefix_prefix_prop (gs: gen_seq_base)
  = forall (s: gs.seq_t) (j:nat{j <= gs.length s}) (i:nat{i <= j}).
        {:pattern gs.prefix (gs.prefix s j) i}
        gs.prefix s i = gs.prefix (gs.prefix s j) i

let gen_seq_spec = gs: gen_seq_base {prefix_prefix_prop gs}

let seq_index (#gs: gen_seq_spec) (s: gs.seq_t) = i:nat{i < gs.length s}

(* an index function is a function that maps indexed elements of a sequence to another domain. *)
let idxfn_t_base (gs: gen_seq_spec) (b:Type0)
  = s:gs.seq_t -> i:seq_index s -> b

(* an index function has a prefix property if the value of the function at an index depends only on the
 * sequence until that index *)
let prefix_property
  (#gs:_)
  (#b:_)
  (f: idxfn_t_base gs b)
  = forall (s: gs.seq_t) (i: seq_index s) (j: nat).
    {:pattern f (gs.prefix s j) i}
    j <= gs.length s ==>
    i < j ==>
    f s i == f (gs.prefix s j) i

(* an index function with the prefix property *)
let idxfn_t (gs:_) (b:_) = f:idxfn_t_base gs b {prefix_property f}

(* conjunction of two index filters *)
let conj #gs (f1 f2: idxfn_t gs bool)
  = fun (s: gs.seq_t) (i: seq_index s) ->
      f1 s i && f2 s i

val conj_is_idxfn (#gs:_) (f1 f2: idxfn_t gs bool)
  : Lemma (ensures (prefix_property (conj f1 f2)))
          [SMTPat (conj f1 f2)]

(* a conditional index function is a function that is defined only some indexes satisfying
 * a predicate *)
let cond_idxfn_t_base (#gs:_) (b:Type0) (f:idxfn_t gs bool)
  = s:gs.seq_t -> i:seq_index s{f s i} -> b

let cond_prefix_property
  (#gs:_)
  (#b:_)
  (#f:idxfn_t gs bool)
  (m: cond_idxfn_t_base b f)
  = forall (s: gs.seq_t) (i:seq_index s) (j: nat).
    {:pattern m (gs.prefix s j) i}
    j <= gs.length s ==>
    i < j ==>
    f s i ==>
    m s i == m (gs.prefix s j) i

let cond_idxfn_t (#gs:_) (b:Type0) (f:idxfn_t gs bool)
  = m:cond_idxfn_t_base b f{cond_prefix_property m}

(* length of applying a filter to *)
val flen (#gs:_) (f: idxfn_t gs bool) (s: gs.seq_t)
  : l:nat{ l <=  gs.length s}

(* map every index satisfying the filter to the index in the filtered sequence *)
val idx2fidx (#gs:_) (f: idxfn_t gs bool) (s: gs.seq_t) (i: seq_index s{f s i})
  : j:nat {j < flen f s}

val fidx2idx (#gs:_) (f: idxfn_t gs bool) (s: gs.seq_t) (j: nat {j < flen f s})
  : i:seq_index s{f s i /\ idx2fidx f s i = j}

val lemma_idx2fidx (#gs:_) (f: idxfn_t gs bool) (s: gs.seq_t) (i: seq_index s{f s i })
  : Lemma (ensures (i = fidx2idx f s (idx2fidx f s i)))
          [SMTPat (idx2fidx f s i)]

val idx2fidx_prefix_property (#gs:_)
  (f: idxfn_t gs bool)
  (s: gs.seq_t)
  (i: seq_index s {f s i})
  (j: nat{j <= gs.length s /\ j > i})
  : Lemma (ensures (idx2fidx f s i = idx2fidx f (gs.prefix s j) i))

val idx2fidx_monotonic (#gs:_)
  (f: idxfn_t gs bool)
  (s: gs.seq_t)
  (i1 i2: (i:seq_index s {f s i}))
  : Lemma (ensures ((i1 < i2 ==> idx2fidx f s i1 < idx2fidx f s i2) /\
                    (i2 < i1 ==> idx2fidx f s i1 > idx2fidx f s i2)))

val fidx2idx_monotonic (#gs:_)
  (f: idxfn_t gs bool)
  (s: gs.seq_t)
  (i1 i2: (i:nat{i < flen f s}))
  : Lemma (ensures ((i1 < i2 ==> fidx2idx f s i1 < fidx2idx f s i2) /\
                    (i2 < i1 ==> fidx2idx f s i1 > fidx2idx f s i2)))

val lemma_fextend_snoc (#gs:_) (f: idxfn_t gs bool) (s: gs.seq_t {gs.length s > 0})
  : Lemma (ensures (let i = gs.length s - 1 in
                    let s' = gs.prefix s i in
                    if f s i then
                      flen f s = flen f s' + 1 /\
                      idx2fidx f s i  = flen f s' /\
                      fidx2idx f s (flen f s') = i
                    else
                      flen f s = flen f s'))

val lemma_idx2fidx_idem (#gs:_) (f: idxfn_t gs bool) (s: gs.seq_t{flen f s = gs.length s}) (i: seq_index s)
  : Lemma (ensures (f s i /\ idx2fidx f s i = i))

(* a specification of a filter-map *)
noeq
type fm_t (gs:_) (b:_) =
  | FM: f: idxfn_t gs bool   ->
        m: cond_idxfn_t b f -> fm_t gs b

let to_fm (#gs:_) (#b:_) (f:idxfn_t gs bool) (m: cond_idxfn_t b f)
  : fm_t gs b
  = FM f m

(* apply the filter fm.f on s to get a filtered sequence; apply fm.m on each element to get the result *)
let filter_map (#gs #b:_)
  (fm: fm_t gs b)
  (s: gs.seq_t)
  : s':seq b {length s' = flen fm.f s}
  = init (flen fm.f s) (fun j -> fm.m s (fidx2idx fm.f s j))

(* map an index of the original sequence to the filter-mapped sequence *)
let filter_map_map (#gs #b:_)
  (fm: fm_t gs b)
  (s: gs.seq_t)
  (i: seq_index s {fm.f s i})
  : j: (SA.seq_index (filter_map fm s)) {index (filter_map fm s) j == fm.m s i /\
        j = idx2fidx fm.f s i}
  = idx2fidx fm.f s i

let filter_map_map_prefix_property (#gs #b:_)
  (fm: fm_t gs b)
  (s: gs.seq_t)
  (i: seq_index s {fm.f s i})
  (j: nat{j <= gs.length s /\ j > i})
  : Lemma (ensures (filter_map_map fm s i = filter_map_map fm (gs.prefix s j) i))
  = idx2fidx_prefix_property fm.f s i j

let lemma_filter_map_map_monotonic (#gs #b:_)
  (fm: fm_t gs b)
  (s: gs.seq_t)
  (i1 i2: (i:seq_index s {fm.f s i}))
  : Lemma (ensures ((i1 < i2 ==> filter_map_map fm s i1 < filter_map_map fm s i2) /\
                    (i1 > i2 ==> filter_map_map fm s i1 > filter_map_map fm s i2)))
  = idx2fidx_monotonic fm.f s i1 i2

(* map an index of the filter-map back to the original sequence *)
let filter_map_invmap (#gs #b:_)
  (fm: fm_t gs b)
  (s: gs.seq_t)
  (j: SA.seq_index (filter_map fm s))
  : i:(seq_index s){fm.f s i /\ filter_map_map fm s i = j /\ i = fidx2idx fm.f s j }
  = fidx2idx fm.f s j

let filter_map_invmap_monotonic (#gs #b:_)
  (fm: fm_t gs b)
  (s: gs.seq_t)
  (j1 j2: SA.seq_index (filter_map fm s))
  : Lemma (ensures (j1 < j2 ==> filter_map_invmap fm s j1 < filter_map_invmap fm s j2) /\
                   (j1 > j2 ==> filter_map_invmap fm s j1 > filter_map_invmap fm s j2))
  = fidx2idx_monotonic fm.f s j1 j2

val lemma_filter_map_extend_sat
  (#gs:_)
  (#b:_)
  (fm: fm_t gs b)
  (s: gs.seq_t {gs.length s > 0 /\ fm.f s (gs.length s - 1)})
  : Lemma (ensures (let fms = filter_map fm s in
                    let fms' = filter_map fm (gs.prefix s (gs.length s - 1)) in
                    let me = fm.m s (gs.length s - 1) in
                    fms == SA.append1 fms' me))
          [SMTPat (filter_map fm s)]

val lemma_filter_map_extend_unsat
  (#gs:_)
  (#b:_)
  (fm: fm_t gs b)
  (s: gs.seq_t {gs.length s > 0 /\ not (fm.f s (gs.length s - 1))})
  : Lemma (ensures (let fms = filter_map fm s in
                    let fms' = filter_map fm (gs.prefix s (gs.length s - 1)) in
                    fms == fms'))
          [SMTPat (filter_map fm s)]

let monotonic (#gs:_) (f: idxfn_t gs bool)
  = forall (s:gs.seq_t) (i1 i2: seq_index s).
        i1 < i2 ==>
        f s i2 ==>
        f s i1

(* return true everywhere; assert(monotonic (all_true gs))*)
let all_true (gs:gen_seq_spec) (s: gs.seq_t) (i:seq_index s)
  = true

val lemma_monotonic_filter (#gs:_)
  (f: idxfn_t gs bool{monotonic f})
  (s: gs.seq_t)
  (i: seq_index s{f s i})
  : Lemma (ensures (idx2fidx f s i = i))
          [SMTPat (idx2fidx f s i)]

let map_fm (#gs:_) (#b:_) (m: idxfn_t gs b)
  : fm_t gs b
  = FM (all_true gs) m

let map (#gs:_) (#b:_) (m: idxfn_t gs b) (s: gs.seq_t)
  : seq b
  = let fm = map_fm m in
    filter_map fm s

val lemma_map_length (#gs:_) (#b:_) (m: idxfn_t gs b) (s: gs.seq_t)
  : Lemma (ensures (length (map m s) = gs.length s))
          [SMTPat (map m s)]

val lemma_map_map
  (#gs:_)
  (#b:_)
  (m: idxfn_t gs b)
  (s: gs.seq_t)
  (i: seq_index s)
  : Lemma (ensures (let fm = map_fm m in
                    filter_map_map fm s i = i))

val lemma_filter_map_monotonic
  (#gs:_)
  (b:_)
  (f:idxfn_t gs bool{monotonic f})
  (fm: fm_t gs b)
  (s: gs.seq_t)
  : Lemma (ensures (filter_map (FM (conj fm.f f) fm.m) s == filter_map fm (gs.prefix s (flen f s))))

val lemma_map_prefix
  (#gs:_)
  (#b:_)
  (f: idxfn_t gs b)
  (s: gs.seq_t)
  (i:nat{i <= gs.length s})
  : Lemma (ensures (SA.prefix (map f s) i == map f (gs.prefix s i)))

let seq_basic (a:eqtype) : gen_seq_spec = {
  seq_t = seq a;
  length;
  prefix = SA.prefix
}

let indexf (#a #b:eqtype) (f: a -> b) (s: seq a) (i: SA.seq_index s)
  : b
  = f (index s i)

let indexm (#a #b:eqtype) (f: a -> bool) (m: (x:a{f x}) -> b) (s: seq a) (i: SA.seq_index s{indexf #_ #bool f s i})
  : b
  = m (index s i)

let simple_fm (#a #b: eqtype) (f: a->bool) (m: (x:a{f x}) -> b)
  : fm_t (seq_basic a) b
  = FM (indexf f) (indexm f m)

let simple_filter_map (#a #b:eqtype) (f: a -> bool) (m: (x:a{f x}) -> b) (s: seq a)
  : seq b
  = let fm = simple_fm f m in
    filter_map fm s

let seqfn_t (gs: gen_seq_spec) (b:_)
  = s:gs.seq_t -> b

let to_pre_fn (#gs #b:_) (f: seqfn_t gs b) (s: gs.seq_t) (i:seq_index s)
  : b
  = let s' = gs.prefix s i in
    f s'

let to_post_fn (#gs #b:_) (f: seqfn_t gs b) (s: gs.seq_t) (i:seq_index s)
  : b
  = let s' = gs.prefix s (i+1) in
    f s'

let simple_map_fm (#a #b: eqtype) (m: a -> b)
  : fm_t (seq_basic a) b
  = let gs : gen_seq_spec = seq_basic a in
    FM (all_true gs) (indexf m)

let simple_map (#a #b: eqtype) (m: a -> b) (s: seq a)
  : seq b
  = let fm = simple_map_fm m in
    filter_map fm s
