module Veritas.Merkle

open FStar.BitVector
open FStar.Seq
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
let rec parent (n:bin_tree_node{~(Root? n)}): Tot bin_tree_node = 
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

(* Traverse down a binary tree from a start node (sn) based on a bit vector *)
let rec traverse_bin_tree (#n:pos) (b:bv_t n) (sn:bin_tree_node): Tot bin_tree_node = 
  let child = if (index b 0) then (LeftChild sn) else (RightChild sn) in  
  if n = 1 
  then child
  else (
    (* TODO: For some reason, replacing pn by (n-1) in recursive call below fails *)
    let pn:pos = (n-1) in
    traverse_bin_tree #pn (slice b 1 n) child)

(* Map a bit vector to a binary tree node by traversing from the root *)
let bv_to_bin_tree_node (#n:pos) (b:bv_t n): Tot bin_tree_node = traverse_bin_tree b Root

(* Traversing adds bit vector length to the depth *)
let rec traverse_adds_size_to_depth (#n:pos) (b:bv_t n) (sn:bin_tree_node): 
  Lemma (requires (True))
        (ensures (depth (traverse_bin_tree b sn) = n + depth sn)) = 
  if (n = 1) then () 
  else (
    let child = if (index b 0) then (LeftChild sn) else (RightChild sn) in
    traverse_adds_size_to_depth #(n-1) (slice b 1 n) child)

(* Depth of the bin tree node of a bit vector is its length *)
let bv_to_bin_tree_node_depth_is_length (#n:pos) (b:bv_t n):
  Lemma (depth (bv_to_bin_tree_node b) = n) = 
  traverse_adds_size_to_depth b Root

let merkle_leaf_addr_of_data (a:addr): Tot merkle_leaf_addr = 
  bv_to_bin_tree_node_depth_is_length a; bv_to_bin_tree_node a

