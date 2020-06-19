module Veritas.Key

open Veritas.BinTree

(* the key space is 2^key_size *)
let key_size = 256

(* key is a bin_tree_node of bounded depth *)
type key = n:bin_tree_node{depth n <= key_size}

(* height of a key *)
let height (k:key) = key_size - depth k

(* 
 * data keys are keys at depth key_size; these are the 
 * keys exposed to an application 
 *)
type data_key = k:key{depth k = key_size}

(* merkle keys are non-data keys *)
type merkle_key = k:key{depth k < key_size}

(* is this a data key *)
let is_data_key (k:key) = depth k = key_size

(* is this a merkle key *)
let is_merkle_key (k:key) = depth k < key_size
