module Zeta.FilterMap

open FStar.Seq
open Zeta.SeqAux

noeq
type filter_map_param_t (a b:_) =
  | FM: f: ((s:seq a{length s > 0}) -> bool) ->
        m: ((s:seq a{length s > 0 /\ f s}) -> b) -> filter_map_param_t a b

let fsat #a #b (fm: filter_map_param_t a b) (s: seq a) (i: seq_index s)
  = fm.f (prefix s (i+1))

let map #a #b (fm: filter_map_param_t a b) (s: seq a) (i: seq_index s{fsat fm s i})
  = fm.m (prefix s (i+1))

val indexed_filter_map (#a #b:_)
  (fm: filter_map_param_t a b)
  (s: seq a)
  : seq b

val indexed_filter_map_map (#a #b:_)
  (fm: filter_map_param_t a b)
  (s: seq a)
  (i: seq_index s {fsat fm s i})
  : j: (seq_index (indexed_filter_map fm s)) {let fms = indexed_filter_map fm s in
                                              index fms j == map fm s i}

val indexed_filter_map_invmap (#a #b:_)
  (fm: filter_map_param_t a b)
  (s: seq a)
  (j: seq_index (indexed_filter_map fm s))
  : i:(seq_index s){ fsat fm s i /\ indexed_filter_map_map fm s i = j }

val lemma_indexed_filter_map (#a #b:_)
  (fm: filter_map_param_t a b)
  (s: seq a)
  (i: seq_index s {fsat fm s i})
  : Lemma (ensures (let j = indexed_filter_map_map fm s i in
                    i = indexed_filter_map_invmap fm s j))
          [SMTPat (indexed_filter_map_map fm s i)]

let tailf #a (f: a -> bool) (s: seq a{length s > 0})
  = f (telem s)

let tailm #a #b (f: a -> bool) (m: (x:a{f x}) -> b) (s: seq a{length s > 0 /\ tailf f s})
  = m (telem s)

let tail_fmparam_t #a #b (f: a -> bool) (m: (x:a{f x}) -> b)
  = FM (tailf f) (tailm f m)

let simple_filter_map (#a #b:_) (f: a -> bool) (m: (x:a {f x}) -> b)
  = indexed_filter_map (tail_fmparam_t f m)

val lemma_filter_map_extend_sat
  (#a #b:_)
  (fm: filter_map_param_t a b)
  (s: seq a {length s > 0 /\ fm.f s})
  : Lemma (ensures (let fms = indexed_filter_map fm s in
                    let fms' = indexed_filter_map fm (hprefix s) in
                    let me = fm.m s in
                    fms == append1 fms' me))
          [SMTPat (indexed_filter_map fm s)]

val lemma_filter_map_extend_unsat
  (#a #b:_)
  (fm: filter_map_param_t a b)
  (s: seq a {length s > 0 /\ not (fm.f s)})
  : Lemma (ensures (let fms = indexed_filter_map fm s in
                    let fms' = indexed_filter_map fm (hprefix s) in
                    fms == fms'))
          [SMTPat (indexed_filter_map fm s)]

val lemma_filter_map_empty
  (#a #b:_)
  (fm: filter_map_param_t a b)
  (s: seq a {length s = 0})
  : Lemma (ensures length (indexed_filter_map fm s) = 0)
          [SMTPat (indexed_filter_map fm s)]
