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

let seq_pred_t_base (a:_) = seq a -> bool

let pred_prefix_property
  (#a:_)
  (p: seq_pred_t_base a)
  = forall (s: seq a) (j:nat).
    {:pattern (prefix s j)}
    j <= length s ==>
    p s ==>
    p (prefix s j)

let seq_pred_t (a:_) = p:seq_pred_t_base a {pred_prefix_property p}

(* an index function is a function that maps indexed elements of a sequence to another domain. *)
let idxfn_t_base (a:_) (pred:seq_pred_t a) (b:eqtype) = s:seq a {pred s} -> i:seq_index s -> b

(* an index function has a prefix property if the value of the function at an index depends only on the
 * sequence until that index *)
let prefix_property
  (#a:_)
  (#pred:_)
  (#b:eqtype)
  (f: idxfn_t_base a pred b)
  = forall (s: seq a {pred s}) (i: nat) (j: nat).
    {:pattern f (prefix s j) i}
    j <= length s ==>
    i < j ==>
    f s i = f (prefix s j) i

(* an index function with the prefix property *)
let idxfn_t (a:_) (pred: seq_pred_t a) (b:eqtype) = f:idxfn_t_base a pred b {prefix_property f}

(* conjunction of two index filters *)
let conj #a #pred (f1 f2: idxfn_t a pred bool)
  = fun (s: seq a{pred s}) (i: seq_index s) ->
      f1 s i && f2 s i

val conj_is_idxfn (#a #pred:_) (f1 f2: idxfn_t a pred bool)
  : Lemma (ensures (prefix_property #a #pred (conj f1 f2)))
          [SMTPat (conj f1 f2)]

(* a conditional index function is a function that is defined only some indexes satisfying
 * a predicate *)
let cond_idxfn_t_base (#a:_) (#pred: seq_pred_t a) (b:eqtype) (f:idxfn_t a pred bool)
  = s:seq a {pred s} -> i:seq_index s{f s i} -> b

let cond_prefix_property
  (#a:_)
  (#pred:seq_pred_t a)
  (#b:_)
  (#f:idxfn_t a pred bool)
  (m: cond_idxfn_t_base b f)
  = forall (s: seq a{pred s}) (i: nat) (j: nat).
    {:pattern m (prefix s j) i}
    j <= length s ==>
    i < j ==>
    f s i ==>
    m s i = m (prefix s j) i

let cond_idxfn_t (#a:_) (#pred: seq_pred_t a) (b:eqtype) (f:idxfn_t a pred bool)
  = m:cond_idxfn_t_base b f{cond_prefix_property m}

(* a specification of a filter-map *)
noeq
type fm_t (a:_) (pred: seq_pred_t a) (b:eqtype) =
  | FM: f: idxfn_t a pred bool   ->
        m: cond_idxfn_t b f -> fm_t a pred b

(* apply the filter fm.f on s to get a filtered sequence; apply fm.m on each element to get the result *)
val filter_map (#a #pred #b:_)
  (fm: fm_t a pred b)
  (s: seq a{pred s})
  : seq b

(* map an index of the original sequence to the filter-mapped sequence *)
val filter_map_map (#a #pred #b:_)
  (fm: fm_t a pred b)
  (s: seq a{pred s})
  (i: seq_index s {fm.f s i})
  : j: (seq_index (filter_map fm s)) {index (filter_map fm s) j == fm.m s i}

val filter_map_map_prefix_property (#a #pred #b:_)
  (fm: fm_t a pred b)
  (s: seq a{pred s})
  (i: seq_index s {fm.f s i})
  (j: nat{j <= length s /\ j > i})
  : Lemma (ensures (filter_map_map fm s i = filter_map_map fm (prefix s j) i))

val lemma_filter_map_map_monotonic (#a #pred #b:_)
  (fm: fm_t a pred b)
  (s: seq a{pred s})
  (i1 i2: (i:seq_index s {fm.f s i}))
  : Lemma (ensures (i1 < i2 ==> filter_map_map fm s i1 < filter_map_map fm s i2))

(* map an index of the filter-map back to the original sequence *)
val filter_map_invmap (#a #pred #b:_)
  (fm: fm_t a pred b)
  (s: seq a{pred s})
  (j: seq_index (filter_map fm s))
  : i:(seq_index s){fm.f s i /\ filter_map_map fm s i = j }

(* the above two index mappings are inverses of one-another *)
val lemma_filter_map (#a #pred #b:_)
  (fm: fm_t a pred b)
  (s: seq a{pred s})
  (i: seq_index s {fm.f s i})
  : Lemma (ensures (let j = filter_map_map fm s i in
                    i = filter_map_invmap fm s j))
          [SMTPat (filter_map_map fm s i)]

val filter_map_invmap_monotonic (#a #pred #b:_)
  (fm: fm_t a pred b)
  (s: seq a{pred s})
  (j1 j2: seq_index (filter_map fm s))
  : Lemma (ensures (j1 < j2 ==> filter_map_invmap fm s j1 < filter_map_invmap fm s j2))

val lemma_filter_map_extend_sat
  (#a:_)
  (#pred:_)
  (#b:eqtype)
  (fm: fm_t a pred b)
  (s: seq a {pred s /\ length s > 0 /\ fm.f s (length s - 1)})
  : Lemma (ensures (let fms = filter_map fm s in
                    let fms' = filter_map fm (hprefix s) in
                    let me = fm.m s (length s - 1) in
                    fms == append1 fms' me))
          [SMTPat (filter_map fm s)]

val lemma_filter_map_extend_unsat
  (#a:_)
  (#pred:_)
  (#b:eqtype)
  (fm: fm_t a pred b)
  (s: seq a {pred s /\ length s > 0 /\ not (fm.f s (length s - 1))})
  : Lemma (ensures (let fms = filter_map fm s in
                    let fms' = filter_map fm (hprefix s) in
                    fms == fms'))
          [SMTPat (filter_map fm s)]

val lemma_filter_map_empty
  (#a:_)
  (#pred:_)
  (#b:eqtype)
  (fm: fm_t a pred b)
  (s: seq a {pred s /\ length s = 0})
  : Lemma (ensures length (filter_map fm s) = 0)
          [SMTPat (filter_map fm s)]

let indexm #a #b (f: a -> bool) (m: (x:a{f x}) -> b) (s: seq a) (i: seq_index s{f (index s i)})
  = m (index s i)

let indexf #a (f: a -> bool) (s: seq a) (i: seq_index s)
  = f (index s i)

let alltrue #a (_:a)
  = true

let simple_fm_t #a (#b:eqtype) (f: a -> bool) (m: (x:a{f x}) -> b)
  : fm_t a (alltrue #(seq a)) b
  = FM (indexf f) (indexm f m)

let simple_filter_map (#a:_) (#b:eqtype) (f: a -> bool) (m: (x:a {f x}) -> b)
  = filter_map (simple_fm_t f m)

let map (#a:_) (#b:_) (f: idxfn_t a (alltrue #(seq a)) b)
  = let fm = FM (indexf alltrue) f in
    filter_map #a #(alltrue #(seq a)) #b fm

let simple_map (#a:_) (#b:eqtype) (m: a -> b)
  = simple_filter_map alltrue m
