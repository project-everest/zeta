module Veritas.Intermediate.Common
open FStar.Integers

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128

type slot_id = n:uint_16{U16.v n < UInt.max_int U16.n}

type u256 = uint_64 & uint_64 & uint_64 & uint_64

type key = u256 & uint_8  //size of a merkle key, excluding leading zeroes


val most_significant_bit (k:key) : bool

let is_data_key (k:key) : bool = most_significant_bit k

val data_t : eqtype //Pick a concrete data value?

let data_value = option data_t

(* size of a hash value *)
let hash_size : nat = 256

(* hash value *)
type hash_value = uint_64 & uint_64 & uint_64 & uint_64

(* information about a desc stored in a merkle node *)
type descendent_hash =
  | Empty: descendent_hash
  | Desc: k:key ->
          h:hash_value ->
          evicted_to_blum:bool ->
          descendent_hash

type value =
  | MVal : l:descendent_hash -> r:descendent_hash -> value
  | DVal : data_value -> value


let is_value_of (k:key) (v:value)
  : bool
  = if is_data_key k then DVal? v else MVal? v

type add_method =
  | MAdd: add_method  (* AddM *)
  | BAdd: add_method  (* AddB *)

type record = {
  record_key:key;
  record_value:value;
  record_add_method:add_method;
  record_l_child_in_store:bool;
  record_r_child_in_store:bool
}


let mk_record k v a : record = {
  record_key = k;
  record_value = v;
  record_add_method = a;
  record_l_child_in_store = false;
  record_r_child_in_store = false;
}

let thread_id_t = uint_16

let timestamp = uint_64

val timestamp_lt (t1 t2: timestamp) : bool

let max (t1 t2: timestamp) =
  if t1 `timestamp_lt` t2 then t2 else t1

let epoch_of_timestamp (t:timestamp)
  : uint_64
  = admit()

noeq
type vlog_entry =
  | Get:     s:slot_id ->
             v:data_value ->
             vlog_entry
  | Put:     s:slot_id ->
             v:data_value ->
             vlog_entry
  | AddM:    s:slot_id ->
             r:record ->
             s':slot_id ->
             vlog_entry
  | EvictM:  s:slot_id ->
             s':slot_id ->
             vlog_entry
  | AddB:    s:slot_id ->
             r:record ->
             t:timestamp ->
             j:thread_id_t ->
             vlog_entry
  | EvictB:  s:slot_id ->
             t:timestamp ->
             vlog_entry
  | EvictBM: s:slot_id ->
             s':slot_id ->
             t:timestamp ->
             vlog_entry
