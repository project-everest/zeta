module Veritas.Merkle

open FStar.BitVector
open Veritas.Memory

(* Nodes in an infinite binary tree *)
type bin_tree_node = 
  | Root: bin_tree_node 
  | LeftChild: n:bin_tree_node -> bin_tree_node
  | RightChild: n:bin_tree_node -> bin_tree_node

(* Depth of a binary tree node *)
let rec depth (n:bin_tree_node): Tot nat = 
  match n with 
  | Root -> 0
  | LeftChild n' -> 1 + depth n'
  | RightChild n' -> 1 + depth n'

(* Parent of a node *)
let parent (n:bin_tree_node{~(Root? n)}): Tot bin_tree_node = 
  match n with
  | LeftChild n' -> n'
  | RightChild n' -> n'

(* Merkle address is simply a bin_tree_node of bounded depth *)
type merkle_addr = n:bin_tree_node{depth n <= addr_size}

(* Depth of a merkle node *)
let merkle_depth (a:merkle_addr): Tot (i:nat {i <= addr_size}) = depth a

(* Height of a merkle node *)
let merkle_height (a:merkle_addr): Tot (i:nat {i <= addr_size}) = addr_size - merkle_depth a

(* Merkle tree root *)
let merkle_root:merkle_addr = Root

(* Is this a merkle root *)
let is_merkle_root (a:merkle_addr): Tot bool = (Root? a)

(* Is this a leaf node *)
let is_merkle_leaf (a:merkle_addr): Tot bool = merkle_height a = 0

(* Helper refinement types of merkle addresses *)
let merkle_leaf_addr = a:merkle_addr{is_merkle_leaf a}
let merkle_root_addr = a:merkle_addr{is_merkle_root a}
let merkle_non_leaf_addr = a:merkle_addr{~(is_merkle_leaf a)}
let merkle_non_root_addr = a:merkle_addr{~(is_merkle_root a)}

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
 * We want to use Merkle tree ideas to verify memory rw-consistency, where
 * memory is addressed locations of a 256-bit address space. To do that we
 * map (data) addresses to leaf nodes of the merkle tree. The leaf node 
 * for a 256-bit address is obtained by traversing the tree from the root 
 * taking a left child for a 0 bit and right child for a 1 bit
 *)

val addr_to_merkle_leaf (a:addr): Tot merkle_leaf_addr

(* Inverse of addr_to_merkle_leaf *)
val merkle_leaf_to_addr (ma:merkle_leaf_addr): Tot (a:addr{addr_to_merkle_leaf a = ma})

val lemma_addr_merkle_inv (a:addr):
  Lemma (merkle_leaf_to_addr (addr_to_merkle_leaf a) = a)

val lemma_merkle_equal_implies_addr_equal (a1:addr) (a2:addr):
  Lemma (requires (addr_to_merkle_leaf a1 = addr_to_merkle_leaf a2))
        (ensures (a1 = a2))

val lemma_addr_equal_implies_merkle_equal (m1:merkle_leaf_addr) (m2:merkle_leaf_addr):
  Lemma (requires (merkle_leaf_to_addr m1 = merkle_leaf_to_addr m2))
        (ensures (m1 = m2))
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
