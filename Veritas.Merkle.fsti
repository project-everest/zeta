module Veritas.Merkle

open FStar.BitVector
open Veritas.BinTree
open Veritas.Memory
open Veritas.MerkleAddr

(* Size of a hash value *)
let hash_size = 256

(* hash_value - bit vector of a specified size *)
type hash_value = bv_t hash_size

(* value stored at specific nodes of a merkle tree *)
type merkle_payload = 
  | MkLeaf: value:payload -> merkle_payload
  | MkInternal: left:hash_value -> right:hash_value -> merkle_payload

let is_payload_of_addr (a:merkle_addr) (p:merkle_payload): Tot bool =
  if is_merkle_leaf a then MkLeaf? p 
  else MkInternal? p

(* merkle payload type conditioned on the address *)
type merkle_payload_of_addr (a:merkle_addr) = 
  p:merkle_payload{is_payload_of_addr a p}

(* hash function maps a merkle payload to a hash value *)
val hashfn (m:merkle_payload): Tot hash_value

(* Inductive type for hash collisions *) 
type hash_collision = 
  | Collision: m1:merkle_payload ->
               m2:merkle_payload { hashfn m1 == hashfn m2 /\ ~(m1 == m2) } ->
               hash_collision

(*
 * merklefn: compute the merkle tree value at each node
 * of the merkle tree
 *)
let rec merklefn (a:merkle_addr) (mem: memory): Tot (merkle_payload_of_addr a)
  (decreases (merkle_height a)) = 
  if is_merkle_leaf a
  then MkLeaf (mem (merkle_leaf_to_addr a))
  else MkInternal (hashfn (merklefn (LeftChild a) mem))
                  (hashfn (merklefn (RightChild a) mem))
        
