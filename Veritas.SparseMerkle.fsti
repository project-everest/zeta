module Veritas.SparseMerkle

open FStar.BitVector
open Veritas.BinTree
open Veritas.MerkleAddr
open Veritas.Memory

(* Size of a hash value *)
let hash_size = 256

(* hash_value - bit vector of a specified size *)
type hash_value = bv_t hash_size

type desc_hash = 
  | Empty: desc_hash
  | Desc: a:merkle_addr -> h:hash_value -> desc_hash

type merkle_payload = 
  | SMkLeaf: value:payload -> merkle_payload
  | SMkInternal: left:desc_hash -> right:desc_hash -> merkle_payload

(* hash function maps a merkle payload to a hash value *)
val hashfn (m:merkle_payload): Tot hash_value

(* Inductive type for hash collisions *) 
type hash_collision = 
  | SCollision: m1:merkle_payload ->
                m2:merkle_payload { hashfn m1 == hashfn m2 /\ ~(m1 == m2) } ->
               hash_collision

let is_payload_of_addr (a:merkle_addr) (p:merkle_payload): Tot bool =
  if is_merkle_leaf a then SMkLeaf? p 
  else SMkInternal? p

(* merkle payload type conditioned on the address *)
type merkle_payload_of_addr (a:merkle_addr) = 
  p:merkle_payload{is_payload_of_addr a p}
