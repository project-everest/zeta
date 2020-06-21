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

let ts_lesser (t1 t2: timestamp) = 
  let e1 = MkTimestamp?.e t1 in
  let c1 = MkTimestamp?.c t1 in
  let e2 = MkTimestamp?.e t2 in
  let c2 = MkTimestamp?.c t2 in
  e1 < e2 || e1 = e2 && c1 < c2

type ms_hashfn_dom = 
  | MHDom: r:record -> t:timestamp -> i:nat -> ms_hashfn_dom

(* 
 * incremental multiset hash function - update the 
 * hash given a new element
 *)
val ms_hashfn_upd (e: ms_hashfn_dom) (h: ms_hash_value): Tot ms_hash_value

(* multiset hash function for a sequence *)
let rec ms_hashfn (s: seq ms_hashfn_dom): Tot ms_hash_value 
  (decreases (length s)) = 
  let n = length s in
  (* empty sequence *)
  if n = 0 then empty_hash_value
  else
    let s' = prefix s (n - 1) in
    let e' = index s (n - 1) in
    let h' = ms_hashfn s' in
    ms_hashfn_upd e' h'

(* two sequences that encode the same multiset produce the same hash *)
val lemma_mshashfn_correct (s1 s2: seq ms_hashfn_dom):
  Lemma (requires (seq2mset s1 == seq2mset s2))
        (ensures (ms_hashfn s1 = ms_hashfn s2))
