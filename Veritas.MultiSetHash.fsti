module Veritas.MultiSetHash

open FStar.BitVector
open FStar.Seq
open Veritas.Key
open Veritas.MultiSet
open Veritas.Record
open Veritas.SeqAux

(* size of a multiset hash value *)
let ms_hash_size = 256

(* multiset hash value *)
type ms_hash_value = bv_t ms_hash_size

(* Hash value of an empty set *)
val empty_hash_value: ms_hash_value

(* timestamp for blum *)
type timestamp = 
  | MkTimestamp: e: nat -> c: nat -> timestamp

let ts_lt (t1 t2: timestamp) = 
  let e1 = MkTimestamp?.e t1 in
  let c1 = MkTimestamp?.c t1 in
  let e2 = MkTimestamp?.e t2 in
  let c2 = MkTimestamp?.c t2 in
  e1 < e2 || e1 = e2 && c1 < c2

let ts_geq (t1 t2: timestamp) = 
  not (ts_lt t1 t2)

let ts_leq (t1 t2: timestamp) = 
  t1 = t2 || t1 `ts_lt` t2

type ms_hashfn_dom = 
  | MHDom: r:record -> t:timestamp -> i:nat -> ms_hashfn_dom

(* 
 * incremental multiset hash function - update the 
 * hash given a new element
 *)
val ms_hashfn_upd (e: ms_hashfn_dom) (h: ms_hash_value): Tot ms_hash_value

(* multiset hash function for a sequence *)
val ms_hashfn (s: seq ms_hashfn_dom): Tot ms_hash_value 

(* two sequences that encode the same multiset produce the same hash *)
val lemma_mshashfn_correct (s1 s2: seq ms_hashfn_dom):
  Lemma (requires (seq2mset s1 == seq2mset s2))
        (ensures (ms_hashfn s1 = ms_hashfn s2))

(* aggregation of multiset hashes *)
val ms_hashfn_agg (h1: ms_hash_value) (h2: ms_hash_value) : Tot ms_hash_value

val lemma_hashfn_agg (s1 s2: seq ms_hashfn_dom):
  Lemma (ms_hashfn (append s1 s2) = ms_hashfn_agg (ms_hashfn s1) (ms_hashfn s2))

(* aggregate a sequence of multiset hashes into a single one *)
val ms_hashfn_agg_seq (hs: seq ms_hash_value): Tot ms_hash_value

(* TODO: Is the correct way to declare this lemma? *)
val lemma_empty_seq (_:unit) :
  Lemma (ms_hashfn_agg_seq FStar.Seq.empty = empty_hash_value)

val lemma_app_seq (hs1 hs2: seq ms_hash_value):
  Lemma (ms_hashfn_agg (ms_hashfn_agg_seq hs1) (ms_hashfn_agg_seq hs2) = 
         ms_hashfn_agg_seq (append hs1 hs2))

(* multiset hash collision *)
type ms_hash_collision = 
  | MSCollision: s1: seq ms_hashfn_dom -> 
                 s2: seq ms_hashfn_dom { ms_hashfn s1 = ms_hashfn s2 /\
                                          ~(seq2mset s1 == seq2mset s2)} -> ms_hash_collision