module Zeta.Key

open Zeta.BinTree

(* the key space is 2^key_size *)
let key_size = 256

(* key is a bin_tree_node of bounded depth *)
let base_key = n:bin_tree_node{depth n <= key_size}

(* height of a key *)
let height (k:base_key) = key_size - depth k

(* 
 * leaf keys are keys of length 256. they correspond to
 * hashes of application keys.
 *)
type leaf_key = k:base_key{depth k = key_size}

(* merkle keys are non-data keys *)
type merkle_key = k:base_key{depth k < key_size}

(* is this a leaf key *)
let is_leaf_key (k:base_key) = depth k = key_size

(* is this a merkle key *)
let is_merkle_key (k:base_key) = depth k < key_size
