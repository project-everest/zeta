module Veritas.Record

open FStar.BitVector
open Veritas.Key

(* data value - add a special value Null over an underlying type a*)
type data_value = 
  | Null: data_value
  | DValue: v:int -> data_value

(* data record is a data_key, data_value pair *)
type data_record = data_key * data_value

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

type merkle_record = merkle_key * merkle_value

(* record - union of data and merkle records *)
type record = 
  | Merkle: m:merkle_record -> record
  | Data: d:data_record -> record
