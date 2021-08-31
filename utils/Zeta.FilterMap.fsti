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

(* prefix property of a map function. *)
let prefix_property
  (#a:_)
  (#b:eqtype)
  (f: (s: seq a -> i:seq_index s -> b))
  = forall (s: seq a) (i: nat) (j: nat).
    {:pattern f (prefix s j) i}
    j <= length s ==>
    i < j ==>
    f s i = f (prefix s j) i

let prefix_property_filter
  (#a:_)
  (#b:eqtype)
  (f: (s:seq a -> i:seq_index s -> bool){prefix_property f})
  (m: (s:seq a -> i:seq_index s {f s i} -> b))
  = forall (s: seq a) (i: nat) (j: nat).
    {:pattern m (prefix s j) i}
    j <= length s ==>
    i < j ==>
    f s i ==>
    m s i = m (prefix s j) i

(* a specification of a filter-map *)
noeq
type fm_t (a:_) (b:eqtype) =
  | FM: f: (s:seq a -> i:seq_index s -> bool) {prefix_property f} ->
        m: (s:seq a -> i:seq_index s{f s i} -> b) {prefix_property_filter f m} -> fm_t a b

(* the filter map from the specification *)
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

(* prefix property of a map function. *)
let ss_prefix_property
  (#a:_)
  (#b:eqtype)
  (p: nat)
  (f: (t:nat{t < p} -> s:seq a -> i:seq_index s -> b))
  = forall (s: seq a) (i: nat) (j: nat) (t: nat).
    {:pattern f t (prefix s j) i}
    j <= length s ==>
    i < j ==>
    t < p ==>
    f t s i = f t (prefix s j) i

let ss_prefix_property_filter
  (#a:_)
  (#b:eqtype)
  (p: nat)
  (f: (t:nat{t < p} -> s:seq a -> i:seq_index s -> bool){ss_prefix_property p f})
  (m: (t:nat{t < p} -> s:seq a -> i:seq_index s{f t s i} -> b))
  = forall (s: seq a) (i: nat) (j: nat) (t: nat).
    {:pattern m t (prefix s j) i}
    j <= length s ==>
    i < j ==>
    t < p ==>
    f t s i ==>
    m t s i = m t (prefix s j) i

(* a specification of a filter-map for sequence of sequences *)
noeq
type ssfm_t (a:_) (b:eqtype) (p:nat) =
  | SSFM: f: (t:nat{t < p} -> s:seq a -> i:seq_index s -> bool) {ss_prefix_property p f} ->
          m: (t:nat{t < p} -> s:seq a -> i:seq_index s{f t s i} -> b){ss_prefix_property_filter p f m} -> ssfm_t a b p

let to_fm_t (#a #b:_) (#p:_) (ssfm: ssfm_t a b p) (t: nat{t < p}): fm_t a b
  = FM (ssfm.f t) (ssfm.m t)

let indexssm #a #b (p:nat) (f: a -> bool) (m: (x:a{f x}) -> b) (t:nat{t < p}) (s: seq a) (i: seq_index s{f (index s i)})
  = m (index s i)

let indexssf #a (p:nat) (f: a -> bool) (t:nat{t < p}) (s: seq a) (i: seq_index s)
  = f (index s i)

let simple_ssfm_t #a (#b:eqtype) (p:nat) (f: a -> bool) (m: (x:a{f x}) -> b)
  : ssfm_t a b p
  = SSFM (indexssf p f) (indexssm p f m)

(* the filter map from the specification *)
val ssfilter_map (#a #b:_) (#p:_)
  (fm: ssfm_t a b p)
  (s: sseq a{length s = p})
  : s':sseq b {length s' = length s}

let simple_ssfilter_map (#a:_) (#b:eqtype) (f: a -> bool) (m: (x:a {f x}) -> b) (s: sseq a)
  = ssfilter_map (simple_ssfm_t (length s) f m) s

(* map an index of the original sequence to the filter-mapped sequence *)
val ssfilter_map_map (#a #b:_) (#p:_)
  (fm: ssfm_t a b p)
  (s: sseq a {length s = p})
  (ii: sseq_index s {let t,i = ii in fm.f t (index s t) i})
  : jj: (sseq_index (ssfilter_map fm s))
    {let t,i = ii in
     indexss (ssfilter_map fm s) jj == fm.m t (index s t) i /\
     fst ii = fst jj}

(* map an index of the filter-map back to the original sequence *)
val ssfilter_map_invmap (#a #b:_) (#p:_)
  (fm: ssfm_t a b p)
  (s: sseq a {length s = p})
  (jj: sseq_index (ssfilter_map fm s))
  : ii:(sseq_index s){let t,i = ii in fm.f t (index s t) i /\ ssfilter_map_map fm s ii = jj }

val lemma_ssfilter_map (#a #b:_) (#p:_)
  (fm: ssfm_t a b p)
  (s: sseq a{length s = p})
  (ii: sseq_index s {let t,i = ii in fm.f t (index s t) i})
  : Lemma (ensures (let jj = ssfilter_map_map fm s ii in
                    ii = ssfilter_map_invmap fm s jj))
          [SMTPat (ssfilter_map_map fm s ii)]

val lemma_ssfilter_map_idx (#a #b:_) (#p:_)
  (ssfm: ssfm_t a b p)
  (ss: sseq a{length ss = p})
  (i: seq_index ss)
  : Lemma (ensures (index (ssfilter_map ssfm ss) i = filter_map (to_fm_t ssfm i) (index ss i)))
