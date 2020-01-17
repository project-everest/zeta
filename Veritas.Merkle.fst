module Veritas.Merkle

open FStar.BitVector
open FStar.Classical
open FStar.Seq
open Veritas.Memory

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

let hashfn (m:merkle_payload): hash_value = admit()

(* 
 * map each 256 bit address in memory to a leaf node of the 
 * merkle tree
 *)
let addr_to_merkle_leaf (a:addr): Tot merkle_leaf_addr = 
  bv_to_bin_tree_node a

(* Inverse of addr_to_merkle_leaf *)
let merkle_leaf_to_addr (ma:merkle_leaf_addr): Tot (a:addr{addr_to_merkle_leaf a = ma}) =
  path_from_root_bv2bin_consistent2 ma; path_from_root ma

let lemma_addr_merkle_inv (a:addr):
  Lemma (merkle_leaf_to_addr (addr_to_merkle_leaf a) = a) = 
  path_from_root_bv2bin_consistent a

let lemma_merkle_equal_implies_addr_equal (a1:addr) (a2:addr):
  Lemma (requires (addr_to_merkle_leaf a1 = addr_to_merkle_leaf a2))
        (ensures (a1 = a2)) = 
  lemma_addr_merkle_inv a1;
  lemma_addr_merkle_inv a2

let lemma_addr_equal_implies_merkle_equal (m1:merkle_leaf_addr) (m2:merkle_leaf_addr):
  Lemma (requires (merkle_leaf_to_addr m1 = merkle_leaf_to_addr m2))
        (ensures (m1 = m2)) = ()
