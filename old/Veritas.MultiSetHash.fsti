module Veritas.MultiSetHash

open FStar.BitVector
open FStar.Seq
open Veritas.Key
open Veritas.MultiSet
open Veritas.Record
open Veritas.SeqAux
include Veritas.MultiSetHashDomain

let u8_hash_value = Seq.lseq UInt8.t 32
val as_ms_hash_value (_:u8_hash_value) : ms_hash_value
val as_u8_hash_value (_:ms_hash_value) : u8_hash_value

(*
 * incremental multiset hash function - update the
 * hash given a new element
 *)
val ms_hashfn_upd (e: ms_hashfn_dom) (h: ms_hash_value): Tot ms_hash_value

(* multiset hash function for a sequence *)
let rec ms_hashfn_aux (s: seq ms_hashfn_dom)
  : Tot ms_hash_value
    (decreases (length s))
  = let n = length s in
    (* empty sequence *)
    if n = 0 then empty_hash_value
    else
      let s' = prefix s (n - 1) in
      let e' = index s (n - 1) in
      let h' = ms_hashfn_aux s' in
      ms_hashfn_upd e' h'

[@@"opaque_to_smt"]
let ms_hashfn = ms_hashfn_aux

let lemma_hashfn_empty (_:unit)
  : Lemma (ms_hashfn (Seq.empty #ms_hashfn_dom) = empty_hash_value)
  = reveal_opaque (`%ms_hashfn) ms_hashfn

let lemma_hashfn_app (s: seq ms_hashfn_dom) (e: ms_hashfn_dom)
  : Lemma (ms_hashfn (append1 s e) = ms_hashfn_upd e (ms_hashfn s))
  = reveal_opaque (`%ms_hashfn) ms_hashfn;
    assert (prefix (append1 s e) (Seq.length s) `Seq.equal` s)

(*** ASSUMPTIONS ABOUT MULTISET HASHES ***)
(* two sequences that encode the same multiset produce the same hash *)
val lemma_mshashfn_correct (s1 s2: seq ms_hashfn_dom):
  Lemma (requires (seq2mset #_ #ms_hashfn_dom_cmp s1 ==
                   seq2mset #_ #ms_hashfn_dom_cmp s2))
        (ensures (ms_hashfn s1 = ms_hashfn s2))

(* aggregation of multiset hashes *)
val ms_hashfn_agg (h1: ms_hash_value) (h2: ms_hash_value) : Tot ms_hash_value

val lemma_hashfn_agg (s1 s2: seq ms_hashfn_dom):
  Lemma (ms_hashfn (append s1 s2) = ms_hashfn_agg (ms_hashfn s1) (ms_hashfn s2))

(* multiset hash collision *)
type ms_hash_collision =
  | MSCollision: s1: seq ms_hashfn_dom ->
                 s2: seq ms_hashfn_dom {
                   ms_hashfn s1 = ms_hashfn s2 /\
                   ~(seq2mset #_ #ms_hashfn_dom_cmp s1 ==
                     seq2mset #_ #ms_hashfn_dom_cmp s2)} ->
                 ms_hash_collision
