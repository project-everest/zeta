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
  (f: a -> bool)
  (m: (s:seq a -> i:seq_index s{f (index s i)} -> b))
  = forall (s: seq a) (i: nat) (j: nat).
    {:pattern m (prefix s j) i}
    j <= length s ==>
    i < j ==>
    f (index s i) ==>
    m s i = m (prefix s j) i

(* a specification of a filter-map *)
noeq
type fm_t (a:_) (b:eqtype) =
  | FM: f: (a -> bool) ->
        m: (s:seq a -> i:seq_index s{f (index s i)} -> b) {prefix_property f m} -> fm_t a b

(* the filter map from the specification *)
val filter_map (#a #b:_)
  (fm: fm_t a b)
  (s: seq a)
  : seq b

(* map an index of the original sequence to the filter-mapped sequence *)
val filter_map_map (#a #b:_)
  (fm: fm_t a b)
  (s: seq a)
  (i: seq_index s {fm.f (index s i)})
  : j: (seq_index (filter_map fm s)) {index (filter_map fm s) j == fm.m s i}

(* map an index of the filter-map back to the original sequence *)
val filter_map_invmap (#a #b:_)
  (fm: fm_t a b)
  (s: seq a)
  (j: seq_index (filter_map fm s))
  : i:(seq_index s){ fm.f (index s i) /\ filter_map_map fm s i = j }

(* the above two index mappings are inverses of one-another *)
val lemma_filter_map (#a #b:_)
  (fm: fm_t a b)
  (s: seq a)
  (i: seq_index s {fm.f (index s i)})
  : Lemma (ensures (let j = filter_map_map fm s i in
                    i = filter_map_invmap fm s j))
          [SMTPat (filter_map_map fm s i)]

let indexm #a #b (f: a -> bool) (m: (x:a{f x}) -> b) (s: seq a) (i: seq_index s{f (index s i)})
  = m (index s i)

let simple_fm_t #a (#b:eqtype) (f: a -> bool) (m: (x:a{f x}) -> b)
  = FM f (indexm f m)

let simple_filter_map (#a:_) (#b:eqtype) (f: a -> bool) (m: (x:a {f x}) -> b)
  = filter_map (simple_fm_t f m)

val lemma_filter_map_extend_sat
  (#a:_)
  (#b:eqtype)
  (fm: fm_t a b)
  (s: seq a {length s > 0 /\ fm.f (telem s)})
  : Lemma (ensures (let fms = filter_map fm s in
                    let fms' = filter_map fm (hprefix s) in
                    let me = fm.m s (length s - 1) in
                    fms == append1 fms' me))
          [SMTPat (filter_map fm s)]

val lemma_filter_map_extend_unsat
  (#a:_)
  (#b:eqtype)
  (fm: fm_t a b)
  (s: seq a {length s > 0 /\ not (fm.f (telem s))})
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
  (f: a -> bool)
  (m: (nat -> s:seq a -> i:seq_index s{f (index s i)} -> b))
  = forall (s: seq a) (i: nat) (j: nat) (t: nat).
    {:pattern m t (prefix s j) i}
    j <= length s ==>
    i < j ==>
    f (index s i) ==>
    m t s i = m t (prefix s j) i

(* a specification of a filter-map for sequence of sequences *)
noeq
type ssfm_t (a:_) (b:eqtype) =
  | SSFM: f: (a -> bool) ->
          m: (j:nat -> s:seq a -> i:seq_index s{f (index s i)} -> b){ss_prefix_property f m} -> ssfm_t a b

let to_fm_t (#a #b:_) (ssfm: ssfm_t a b) (t: nat): fm_t a b
  = FM ssfm.f (ssfm.m t)

(* the filter map from the specification *)
val ssfilter_map (#a #b:_)
  (fm: ssfm_t a b)
  (s: sseq a)
  : s':sseq b {length s' = length s}

(* map an index of the original sequence to the filter-mapped sequence *)
val ssfilter_map_map (#a #b:_)
  (fm: ssfm_t a b)
  (s: sseq a)
  (ii: sseq_index s {fm.f (indexss s ii)})
  : jj: (sseq_index (ssfilter_map fm s))
    {let t,i = ii in
     indexss (ssfilter_map fm s) jj == fm.m t (index s t) i /\
     fst ii = fst jj}

(* map an index of the filter-map back to the original sequence *)
val ssfilter_map_invmap (#a #b:_)
  (fm: ssfm_t a b)
  (s: sseq a)
  (jj: sseq_index (ssfilter_map fm s))
  : ii:(sseq_index s){ fm.f (indexss s ii) /\ ssfilter_map_map fm s ii = jj }

val lemma_ssfilter_map (#a #b:_)
  (fm: ssfm_t a b)
  (s: sseq a)
  (ii: sseq_index s {fm.f (indexss s ii)})
  : Lemma (ensures (let jj = ssfilter_map_map fm s ii in
                    ii = ssfilter_map_invmap fm s jj))
          [SMTPat (ssfilter_map_map fm s ii)]

val lemma_ssfilter_map_idx (#a #b:_)
  (ssfm: ssfm_t a b)
  (ss: sseq a)
  (i: seq_index ss)
  : Lemma (ensures (index (ssfilter_map ssfm ss) i = filter_map (to_fm_t ssfm i) (index ss i)))
