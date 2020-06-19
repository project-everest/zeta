module Veritas.Record

open FStar.BitVector
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
  | Desc: k:merkle_key -> h:hash_value -> b:bool -> desc_hash

(* merkle value: information about left and right descendants *)
type merkle_value = 
  | MValue: l:desc_hash -> r:desc_hash -> merkle_value

(* value - union type of merkle and data values *)
type value = 
  | Merkle: v:merkle_value -> value
  | Data: v:data_value -> value

(* check merkle/data consistency of k and v *)
let is_value_of (k:key) (v:value) = 
  if is_data_key k then Data? v
  else Merkle? v

type value_type_of (k:key) = v:value{is_value_of k v}

type key_type_of (v:value) = k:key{is_value_of k v}

(* record - key-value pair *)
type record = key * value
