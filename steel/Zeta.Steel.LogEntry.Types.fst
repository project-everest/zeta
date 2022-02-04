module Zeta.Steel.LogEntry.Types
open Zeta.Steel.ApplicationRecord

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

let significant_digits_t = significant_digits: U16.t { U16.v significant_digits <= 256 }

noeq 
type uninterpreted = {
 //  offset:U32.t; We'll need to know the offset in the input buffer where these bytes occur
 //  but this is probably not the place to stash it
  len: (len: U32.t { U32.v len < 2147483648 }); // FIXME: arbitrary bound due to the use of FStar.Bytes
  ebytes: (ebytes: Ghost.erased (Seq.seq U8.t) { Seq.length ebytes == U32.v len });
}

type timestamp = U64.t

type thread_id = U16.t

type u256 = {
  v3 : U64.t;
  v2 : U64.t;
  v1 : U64.t;
  v0 : U64.t;
}

type base_key = {
  k: u256;
  significant_digits : significant_digits_t;
}

let internal_key = k: base_key { U16.v k.significant_digits < 256 }

let hash_value = u256

type vbool =
  | Vfalse
  | Vtrue

type descendent_hash_desc = {
  dhd_key : base_key;
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
type evictM_payload = {
      s:slot_id;
      s_:slot_id;
}

noeq
type evictB_payload = {
  s:slot_id;
  t:timestamp;
}

noeq
type evictBM_payload = {
  s:slot_id;
  s_:slot_id;  
  t:timestamp;
}

noeq
type runApp_payload = {
  fid:U8.t;
  rest:uninterpreted
}

type value = 
  | MValue of mval_value
  | DValue of option value_type

let is_value_of (k:key) (v:value)
  : bool
  = if ApplicationKey? k then DValue? v else MValue? v

let record = (r: (key & value) { is_value_of (fst r) (snd r) })

open Zeta.Steel.Parser

noeq
type log_entry =
  | AddM : s:slot_id ->
           s_:slot_id ->
           r:record ->
           log_entry

  | AddB : s:slot_id ->
           ts:timestamp ->
           tid:thread_id ->
           r:record ->
           log_entry

  | RunApp of runApp_payload
  | EvictM of evictM_payload
  | EvictB of evictB_payload
  | EvictBM of evictBM_payload
  | NextEpoch
  | VerifyEpoch

type stamped_record = {
  record : record;
  timestamp : timestamp;
  thread_id : thread_id;
}
