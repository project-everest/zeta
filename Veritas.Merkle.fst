module Veritas.Merkle

open FStar.BitVector
open FStar.Classical
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

(* Size of a hash value *)
let hash_size = 256

(* hash_value - bit vector of a specified size *)
type hash_value = bv_t hash_size

(* value stored at specific nodes of a merkle tree *)
type merkle_payload = 
  | MkLeaf: value:payload -> merkle_payload
  | MkInternal: left:hash_value -> right:hash_value -> merkle_payload

(* hash function maps a merkle payload to a hash value *)
assume val hashfn (m:merkle_payload): hash_value

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

(* Traverse down a binary tree from a start node (sn) based on a bit vector *)
let rec traverse_bin_tree (#n:pos) (b:bv_t n) (sn:bin_tree_node): Tot bin_tree_node = 
  if n = 1 
  then if index b 0 then RightChild sn else LeftChild sn
  else (
    let tn' = traverse_bin_tree #(n-1) (slice b 0 (n-1)) sn in
    if index b (n-1) then RightChild tn' else LeftChild tn'
  )

(* Traversing adds bit vector length to the depth *)
let rec traverse_adds_size_to_depth (#n:pos) (b:bv_t n) (sn:bin_tree_node): 
  Lemma (requires (True))
        (ensures (depth (traverse_bin_tree b sn) = n + depth sn)) = 
  if (n = 1) 
  then () 
  else traverse_adds_size_to_depth #(n-1) (slice b 0 (n-1)) sn

(* Map a bit vector to a binary tree node by traversing from the root *)
let bv_to_bin_tree_node (#n:pos) (b:bv_t n): Tot (t:bin_tree_node{depth t = n}) = 
  traverse_adds_size_to_depth b Root; traverse_bin_tree b Root

(* Given a binary tree node return the path from root as a binary vector *)
let rec path_from_root (a:bin_tree_node{depth a > 0}): Tot (b:bv_t (depth a)) 
  (decreases (depth a)) = 
  if depth a = 1 
  then (match a with
       | LeftChild a' -> zero_vec #1
       | RightChild a' -> ones_vec #1
       )
  else (match a with
       | LeftChild a' -> (append (path_from_root a') (zero_vec #1))
       | RightChild a' -> (append (path_from_root a') (ones_vec #1))
       )

(* path_from_root and bv_to_bin_tree_node are inverse operations *)
let rec path_from_root_bv2bin_consistent_aux (#n:pos) (b:bv_t n) (i:nat{i < n}):
  Lemma (index (path_from_root (bv_to_bin_tree_node b)) i = index b i)
  = 
  if n = 1 then ()  
  else (
    if i = n - 1 
    then ()
    else path_from_root_bv2bin_consistent_aux #(n-1) (slice b 0 (n-1)) i
  )

(* path_from_root and bv_to_bin_tree_node are inverse operations *)
let path_from_root_bv2bin_consistent (#n:pos) (b:bv_t n):
  Lemma (path_from_root (bv_to_bin_tree_node b) = b) = 
  let b' = path_from_root (bv_to_bin_tree_node b) in
  let aux (i:nat{i < n}): Lemma ((index b' i) = (index b i)) = 
    path_from_root_bv2bin_consistent_aux b i  
  in
  forall_intro aux; lemma_eq_intro b b'

(* path_from_root and bv_to_bin_tree_node are inverse operations - II *)
let rec path_from_root_bv2bin_consistent2 (tn:bin_tree_node{depth tn > 0}):
  Lemma (requires (True)) 
        (ensures bv_to_bin_tree_node (path_from_root tn) = tn)
  (decreases (depth tn)) =
  let n = depth tn in
  if n = 1 then ()
  else match tn with 
       | LeftChild tn' -> 
           let p' = path_from_root tn' in
           append_slices p' (zero_vec #1);
           path_from_root_bv2bin_consistent2 tn'
       | RightChild tn' -> 
           let p' = path_from_root tn' in
           append_slices p' (ones_vec #1);
           path_from_root_bv2bin_consistent2 tn'

(* 
 * map each 256 bit address in memory to a leaf node of the 
 * merkle tree
 *)
let addr_to_merkle_leaf (a:addr): Tot merkle_leaf_addr = 
  bv_to_bin_tree_node a

(* Inverse of addr_to_merkle_leaf *)
let merkle_leaf_to_addr (a:merkle_leaf_addr): Tot addr = path_from_root a

(*
 * merklefn: compute the merkle tree value at each node
 * of the merkle tree
 *)
let rec merklefn (a:merkle_addr) (mem: memory): Tot merkle_payload
  (decreases (merkle_height a)) = 
  if is_merkle_leaf a
  then MkLeaf (mem (path_from_root a))
  else MkInternal (hashfn (merklefn (LeftChild a) mem))
                  (hashfn (merklefn (RightChild a) mem))

