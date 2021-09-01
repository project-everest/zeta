module Zeta.FilterMap

open FStar.Seq
open Zeta.SeqAux
open Zeta.SSeq

(*
 * a common pattern that appears in many parts of Zeta proof is "filter-map" pattern:
 *   we apply a filter on the elements of the original sequence and map
 *   the resulting sequence to another domain.
 *
 * A generalization of the filter-map is when the map-function depends
 * on the prefix of the sequence, not just the element. E.g., the blum-evict element
 * on a verifier log is defined for log entries that are blum-evicts, but the evict
 * element contains a timestamp which depends on the entire history of the log until
 * that position.  *)

(* an index function is a function that maps indexed elements of a sequence to another domain. *)
let idxfn_t_base (a:_) (b:eqtype) = s:seq a -> i:seq_index s -> b

(* an index function has a prefix property if the value of the function at an index depends only on the
 * sequence until that index *)
let prefix_property
  (#a:_)
  (#b:eqtype)
  (f: idxfn_t_base a b)
  = forall (s: seq a) (i: nat) (j: nat).
    {:pattern f (prefix s j) i}
    j <= length s ==>
    i < j ==>
    f s i = f (prefix s j) i

(* an index function with the prefix property *)
let idxfn_t (a:_) (b:eqtype) = f:idxfn_t_base a b {prefix_property f}

(* a conditional index function is a function that is defined only some indexes satisfying
 * a predicate *)
let cond_idxfn_t_base (#a:_) (b:eqtype) (f:idxfn_t a bool)
  = s:seq a -> i:seq_index s{f s i} -> b

let cond_prefix_property
  (#a:_)
  (#b:_)
  (#f:_)
  (m: cond_idxfn_t_base b f)
  = forall (s: seq a) (i: nat) (j: nat).
    {:pattern m (prefix s j) i}
    j <= length s ==>
    i < j ==>
    f s i ==>
    m s i = m (prefix s j) i

let cond_idxfn_t (#a:_) (b:eqtype) (f:idxfn_t a bool)
  = m:cond_idxfn_t_base b f{cond_prefix_property m}

(* a specification of a filter-map *)
noeq
type fm_t (a:_) (b:eqtype) =
  | FM: f: _   ->
        m: cond_idxfn_t #a b f -> fm_t a b

(* apply the filter fm.f on s to get a filtered sequence; apply fm.m on each element to get the result *)
val filter_map (#a #b:_)
  (fm: fm_t a b)
  (s: seq a)
  : seq b

(* map an index of the original sequence to the filter-mapped sequence *)
val filter_map_map (#a #b:_)
  (fm: fm_t a b)
  (s: seq a)
  (i: seq_index s {fm.f s i})
  : j: (seq_index (filter_map fm s)) {index (filter_map fm s) j == fm.m s i}

(* map an index of the filter-map back to the original sequence *)
val filter_map_invmap (#a #b:_)
  (fm: fm_t a b)
  (s: seq a)
  (j: seq_index (filter_map fm s))
  : i:(seq_index s){fm.f s i /\ filter_map_map fm s i = j }

(* the above two index mappings are inverses of one-another *)
val lemma_filter_map (#a #b:_)
  (fm: fm_t a b)
  (s: seq a)
  (i: seq_index s {fm.f s i})
  : Lemma (ensures (let j = filter_map_map fm s i in
                    i = filter_map_invmap fm s j))
          [SMTPat (filter_map_map fm s i)]

let indexm #a #b (f: a -> bool) (m: (x:a{f x}) -> b) (s: seq a) (i: seq_index s{f (index s i)})
  = m (index s i)

let indexf #a (f: a -> bool) (s: seq a) (i: seq_index s)
  = f (index s i)

let simple_fm_t #a (#b:eqtype) (f: a -> bool) (m: (x:a{f x}) -> b)
  = FM (indexf f) (indexm f m)

let simple_filter_map (#a:_) (#b:eqtype) (f: a -> bool) (m: (x:a {f x}) -> b)
  = filter_map (simple_fm_t f m)

val lemma_filter_map_extend_sat
  (#a:_)
  (#b:eqtype)
  (fm: fm_t a b)
  (s: seq a {length s > 0 /\ fm.f s (length s - 1)})
  : Lemma (ensures (let fms = filter_map fm s in
                    let fms' = filter_map fm (hprefix s) in
                    let me = fm.m s (length s - 1) in
                    fms == append1 fms' me))
          [SMTPat (filter_map fm s)]

val lemma_filter_map_extend_unsat
  (#a:_)
  (#b:eqtype)
  (fm: fm_t a b)
  (s: seq a {length s > 0 /\ not (fm.f s (length s - 1))})
  : Lemma (ensures (let fms = filter_map fm s in
                    let fms' = filter_map fm (hprefix s) in
                    fms == fms'))
          [SMTPat (filter_map fm s)]

val lemma_filter_map_empty
  (#a:_)
  (#b:eqtype)
  (fm: fm_t a b)
  (s: seq a {length s = 0})
  : Lemma (ensures length (filter_map fm s) = 0)
          [SMTPat (filter_map fm s)]

(* we are interested in sequence of sequences and index functions over the inner sequence.
 * one subtlety is we want the indexed functions over the inner sequence to not be fixed but
 * dependent on the index of the sequence in the sequence of sequences. *)

let sidxfn_t_base (p:nat) (a:_) (b:eqtype) = (t:nat{t < p}) -> s:seq a -> seq_index s -> b

let s_prefix_property
  (#p:_)
  (#a:_)
  (#b:_)
  (f: sidxfn_t_base p a b)
  = forall (s: seq a) (i: nat) (j: nat) (t: nat).
    {:pattern f t (prefix s j) i}
    j <= length s ==>
    i < j ==>
    t < p ==>
    f t s i = f t (prefix s j) i

let sidxfn_t (p:nat) (a:_) (b:eqtype)  = f:sidxfn_t_base p a b {s_prefix_property f}

let ssfn #p #a #b (f:sidxfn_t p a b) (ss: sseq a{length ss = p}) (ti: sseq_index ss)
  = let t,i = ti in
    f t (index ss t) i

let scond_idxfn_t_base (#p:_) (#a:_) (b:eqtype) (f:sidxfn_t p a bool)
  = t:nat{t < p} -> s:seq a -> i: seq_index s {f t s i} -> b

let s_cond_prefix_property
  (#p:_)
  (#a:_)
  (#b:_)
  (#f:sidxfn_t p a bool)
  (m: scond_idxfn_t_base b f)
  = forall (s: seq a) (i: nat) (j: nat) (t: nat).
    {:pattern m t (prefix s j) i}
    j <= length s ==>
    i < j ==>
    t < p ==>
    f t s i ==>
    m t s i = m t (prefix s j) i

let scond_idxfn_t #p #a (b:_) (f:sidxfn_t p a bool)
  = m:scond_idxfn_t_base b f{s_cond_prefix_property m}

let cond_ssfn #p #a #b (#f:sidxfn_t p a bool) (m:scond_idxfn_t b f)
  (ss: sseq a{length ss = p}) (ti: sseq_index ss{ssfn f ss ti})
  = let t,i = ti in
    m t (index ss t) i

(* a specification of a filter-map for sequence of sequences *)
noeq
type ssfm_t (p:nat) (a:_) (b:eqtype) =
  | SSFM: f: _  ->
          m: scond_idxfn_t #p #a b f -> ssfm_t p a b

let to_fm_t (#p:_) (#a #b:_) (ssfm: ssfm_t p a b) (t: nat{t < p}): fm_t a b
  = FM (ssfm.f t) (ssfm.m t)

let indexssm #a #b (p:nat) (f: a -> bool) (m: (x:a{f x}) -> b) (t:nat{t < p}) (s: seq a) (i: seq_index s{f (index s i)})
  = m (index s i)

let indexssf #a (p:nat) (f: a -> bool) (t:nat{t < p}) (s: seq a) (i: seq_index s)
  = f (index s i)

let simple_ssfm_t #a (#b:eqtype) (p:nat) (f: a -> bool) (m: (x:a{f x}) -> b)
  : ssfm_t p a b
  = SSFM (indexssf p f) (indexssm p f m)

(* the filter map from the specification *)
val ssfilter_map (#p:_) (#a #b:_)
  (fm: ssfm_t p a b)
  (s: sseq a{length s = p})
  : s':sseq b {length s' = length s}

let simple_ssfilter_map (#a:_) (#b:eqtype) (f: a -> bool) (m: (x:a {f x}) -> b) (s: sseq a)
  = ssfilter_map (simple_ssfm_t (length s) f m) s

(* map an index of the original sequence to the filter-mapped sequence *)
val ssfilter_map_map (#p:_) (#a #b:_)
  (fm: ssfm_t p a b)
  (s: sseq a {length s = p})
  (ii: sseq_index s {ssfn fm.f s ii})
  : jj: (sseq_index (ssfilter_map fm s))
    {indexss (ssfilter_map fm s) jj == cond_ssfn fm.m s ii /\
     fst ii = fst jj}

(* map an index of the filter-map back to the original sequence *)
val ssfilter_map_invmap (#p:_) (#a #b:_)
  (fm: ssfm_t p a b)
  (s: sseq a {length s = p})
  (jj: sseq_index (ssfilter_map fm s))
  : ii:(sseq_index s){ssfn fm.f s ii /\ ssfilter_map_map fm s ii = jj }

val lemma_ssfilter_map (#p:_) (#a #b:_)
  (fm: ssfm_t p a b)
  (s: sseq a{length s = p})
  (ii: sseq_index s {ssfn fm.f s ii})
  : Lemma (ensures (let jj = ssfilter_map_map fm s ii in
                    ii = ssfilter_map_invmap fm s jj))
          [SMTPat (ssfilter_map_map fm s ii)]

val lemma_ssfilter_map_idx (#p:_) (#a #b:_)
  (ssfm: ssfm_t p a b)
  (ss: sseq a{length ss = p})
  (i: seq_index ss)
  : Lemma (ensures (index (ssfilter_map ssfm ss) i = filter_map (to_fm_t ssfm i) (index ss i)))
