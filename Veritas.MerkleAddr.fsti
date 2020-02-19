module Veritas.MerkleAddr

open Veritas.BinTree
open Veritas.Memory

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
