module Veritas.Intermediate.Common
open FStar.Integers

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128
open Veritas.Record
type slot_id = nat

let key = Veritas.Key.key

val most_significant_bit (k:key) : bool

let value = Veritas.Record.value

let add_method = Veritas.Verifier.add_method

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

let thread_id_t = nat

let timestamp = Veritas.MultiSetHash.timestamp

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
