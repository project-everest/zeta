module Veritas.MerkleAddr

open FStar.BitVector
open Veritas.BinTree

(* 
 * map each 256 bit address in memory to a leaf node of the 
 * merkle tree
 *)
let addr_to_merkle_leaf (a:addr): Tot merkle_leaf_addr = 
  bv_to_bin_tree_node a

(* Inverse of addr_to_merkle_leaf *)
let merkle_leaf_to_addr (ma:merkle_leaf_addr): Tot (a:addr{addr_to_merkle_leaf a = ma}) =
  bin_tree_to_bv_consistent ma; bin_tree_node_to_bv ma

let lemma_addr_merkle_inv (a:addr):
  Lemma (merkle_leaf_to_addr (addr_to_merkle_leaf a) = a) = 
  bv_to_bin_tree_consistent a

let lemma_merkle_addr_inv (ma:merkle_leaf_addr):
  Lemma (requires (True))
        (ensures (addr_to_merkle_leaf (merkle_leaf_to_addr ma) = ma))
        [SMTPat (merkle_leaf_to_addr ma)] = 
  let a = merkle_leaf_to_addr ma in
  ()

let lemma_merkle_equal_implies_addr_equal (a1:addr) (a2:addr):
  Lemma (requires (addr_to_merkle_leaf a1 = addr_to_merkle_leaf a2))
        (ensures (a1 = a2)) = 
  lemma_addr_merkle_inv a1;
  lemma_addr_merkle_inv a2

let lemma_addr_equal_implies_merkle_equal (m1:merkle_leaf_addr) (m2:merkle_leaf_addr):
  Lemma (requires (merkle_leaf_to_addr m1 = merkle_leaf_to_addr m2))
        (ensures (m1 = m2)) = ()

