
module Veritas.Record

open FStar.BitVector
open Veritas.BinTree
open Veritas.Key

(* data value - add a special value Null over an underlying type a*)
type data_value = 
  | Null: data_value
  | DValue: v:int -> data_value

(* size of a hash value *)
let hash_size = 256

(* hash value *)
type hash_value = bv_t hash_size

(* information about a desc stored in a merkle node *)
type desc_hash = 
  | Empty: desc_hash
  | Desc: k:key -> h:hash_value -> b:bool -> desc_hash

(* merkle value: information about left and right descendants *)
type merkle_value = 
  | MkValue: l:desc_hash -> r:desc_hash -> merkle_value

let desc_hash_dir (v:merkle_value) (d:bin_tree_dir) = 
  match d with
  | Left -> MkValue?.l v
  | Right -> MkValue?.r v
  
(* value - union type of merkle and data values *)
type value = 
  | MVal: v:merkle_value -> value
  | DVal: v:data_value -> value

(* check merkle/data consistency of k and v *)
let is_value_of (k:key) (v:value) = 
  if is_data_key k then DVal? v
  else MVal? v

type value_type_of (k:key) = v:value{is_value_of k v}

type key_type_of (v:value) = k:key{is_value_of k v}

(* record - key-value pair *)
type record = key * value

let init_value (k:key): v:value{is_value_of k v} = 
  if is_data_key k then DVal Null
  else MVal (MkValue Empty Empty)

let to_merkle_value (v:value{MVal? v}) = MVal?.v v

let to_data_value (v:value{DVal? v}) = DVal?.v v
