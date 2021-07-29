module Zeta.Steel.FormatsManual
(* This file should eventually be generated by EverParse and renamed
   to Zeta.Steel.Formats *)
open FStar.Ghost
open Zeta.Steel.ApplicationTypes
module A = Zeta.App
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

let significant_digits_t = significant_digits: U16.t { U16.v significant_digits <= 256 }

noeq 
type uninterpreted = {
 //  offset:U32.t; We'll need to know the offset in the input buffer where these bytes occur
 //  but this is probably not the place to stash it
  len:U32.t;
  ebytes: erased (Seq.seq U8.t)
}

type timestamp = U64.t

type thread_id = U16.t

type u256 = {
  v3 : U64.t;
  v2 : U64.t;
  v1 : U64.t;
  v0 : U64.t;
}

type internal_key = {
  k : u256;
  significant_digits : significant_digits_t;
}
  
let hash_value = u256

type vbool =
  | Vfalse
  | Vtrue

type descendent_hash_desc = {
  dhd_key : internal_key;
  dhd_h : hash_value;
  evicted_to_blum : vbool;
}

type descendent_hash =
  | Dh_vnone of unit
  | Dh_vsome of descendent_hash_desc

type value_kind =
  | Mval
  | Dval

type mval_value = {
  l : descendent_hash;
  r : descendent_hash;
}

let slot_id = U16.t

type key = 
  | InternalKey of internal_key
  | ApplicationKey of key_type

noeq
type addM_payload = {
      k:key;
      v:mval_value;
      s:slot_id;
      s':slot_id;
}

noeq
type addMApp_payload = {
      s:slot_id;
      s':slot_id;
      rest:uninterpreted
}

noeq
type addBApp_payload = {
      s:slot_id;
      t:timestamp;
      tid:thread_id;
      rest:uninterpreted
}

noeq
type addB_payload = {
      k:key;
      v:mval_value;
      s:slot_id;
      t:timestamp;
      tid:thread_id;
}

noeq
type evictM_payload = {
      s:slot_id;
      s':slot_id;
}

noeq
type evictB_payload = {
  s:slot_id;
  t:timestamp;
}

noeq
type evictBM_payload = {
  s:slot_id;
  s':slot_id;  
  t:timestamp;
}

noeq
type runApp_payload = {
  fid:U8.t;
  rest:uninterpreted
}

//remove the _base from the name
noeq
type log_entry_base =
  | AddM of addM_payload
  | AddB of addB_payload
  | EvictM of evictM_payload
  | EvictB of evictB_payload
  | EvictBM of evictBM_payload
  | NextEpoch of unit
  | VerifyEpoch of unit
  | AddMApp of addMApp_payload
  | AddBApp of addBApp_payload
  | RunApp of runApp_payload

/// Factored into another module?

let slot = x:slot_id{ U16.v x < U16.v store_size }

let is_internal_key_for_data (k:internal_key)
  : bool
  = k.significant_digits = 256us

let is_internal_key_root (k:internal_key) 
  : bool
  = k.significant_digits = 0us

type value = 
  | MValue of mval_value
  | DValue of option value_type

let record = key & value

type stamped_record = {
  record : record;
  timestamp : timestamp;
  thread_id : thread_id;
}

module P = Zeta.Steel.Parser
val spec_parser_app_record: P.spec_parser (key_type & option value_type)
val parse_app_record: P.parser spec_parser_app_record

val spec_parser_stamped_record : P.spec_parser stamped_record
val spec_serializer_stamped_record : P.spec_serializer spec_parser_stamped_record
val serialize_stamped_record : P.serializer spec_serializer_stamped_record

/// This is an ad hoc bound due to a bound on Blake hashable inputs
val serialized_stamped_record_length (s:stamped_record)
  : Lemma (Seq.length (spec_serializer_stamped_record s) <= 8192)
