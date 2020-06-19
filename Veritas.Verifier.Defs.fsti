module Veritas.Verifier.Defs

open FStar.BitVector
open FStar.Seq
open Veritas.BinTree
open Veritas.MerkleAddr
open Veritas.Memory
open Veritas.MultiSet
open Veritas.SeqAux

(* size of a hash value *)
let hash_size = 256

(* hash value *)
type hash_value = bv_t hash_size

type desc_hash = 
  | Empty: desc_hash
  | Desc: a:merkle_addr -> h:hash_value -> b:bool -> desc_hash

type merkle_payload = 
  | MkLeaf: value: payload -> merkle_payload
  | MkInternal: left: desc_hash -> right: desc_hash -> merkle_payload

let is_payload_of_addr (a:merkle_addr) (p:merkle_payload): Tot bool = 
  if is_merkle_leaf a then MkLeaf? p
  else MkInternal? p

(* merkle payload type conditioned on address *)
type merkle_payload_of_addr (a:merkle_addr) = 
  p:merkle_payload{is_payload_of_addr a p}

(* payload of an internal node *)
type merkle_payload_internal = p:merkle_payload { MkInternal? p }

(* get the descendant hash of a specified direction *)
let desc_hash_dir (c: bin_tree_dir) (p:merkle_payload_internal): desc_hash = 
  match c with
  | Left -> MkInternal?.left p
  | Right -> MkInternal?.right p

(* hash function maps a merkle payload to a hash value *)
val hashfn (m:merkle_payload): Tot hash_value

(* timestamps for blum hashing *)
type timestamp = 
  | MkTimestamp: e: nat -> c: nat -> timestamp

(* multi-set hash value *)
type ms_hash_value = hash_value

(* Hash value of an empty set *)
val empty_hash_value: ms_hash_value

(* domain of multiset hash function *)
type ms_hashfn_dom = 
  | MsHashDom: 
    a:merkle_addr -> 
    p: merkle_payload_of_addr a -> 
    t: timestamp -> 
    i: nat -> ms_hashfn_dom

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

