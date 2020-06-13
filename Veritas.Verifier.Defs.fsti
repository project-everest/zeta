module Veritas.Verifier.Defs

open FStar.BitVector
open Veritas.BinTree
open Veritas.MerkleAddr
open Veritas.Memory

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
  | MkTimestamp: epoch: nat -> counter: nat -> timestamp

(* multi-set hash value *)
type ms_hash_value = hash_value

(* Hash value of an empty set *)
val empty_hash_value: ms_hash_value

