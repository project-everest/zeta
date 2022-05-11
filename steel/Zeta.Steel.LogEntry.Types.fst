module Zeta.Steel.LogEntry.Types
open Zeta.Steel.ApplicationRecord
include Zeta.Steel.KeyUtils
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module KU = Zeta.Steel.KeyUtils


// let significant_digits_t = significant_digits: U16.t { U16.v significant_digits <= 256 }

noeq 
type uninterpreted = {
 //  offset:U32.t; We'll need to know the offset in the input buffer where these bytes occur
 //  but this is probably not the place to stash it
  len: (len: U32.t { U32.v len < 2147483648 }); // FIXME: arbitrary bound due to the use of FStar.Bytes
  ebytes: (ebytes: Ghost.erased (Seq.seq U8.t) { Seq.length ebytes == U32.v len });
}

type timestamp = {
  epoch:U32.t;
  counter: U32.t
}

type thread_id = U16.t

let hash_value = KU.u256

type vbool =
  | Vfalse
  | Vtrue

noeq
type descendent_hash_desc = {
  dhd_key : base_key;
  dhd_h : hash_value;
  evicted_to_blum : vbool;
}

noeq
type descendent_hash =
  | Dh_vnone of unit
  | Dh_vsome of descendent_hash_desc

type value_kind =
  | Mval
  | Dval

noeq
type mval_value = {
  l : descendent_hash;
  r : descendent_hash;
}

let slot_id = U16.t

noeq
type key = 
  | InternalKey of internal_key
  | ApplicationKey of key_type

inline_for_extraction
let root_key = InternalKey KU.root_base_key

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

noeq
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

noeq
type stamped_record = {
  record : record;
  timestamp : timestamp;
  thread_id : thread_id;
}
