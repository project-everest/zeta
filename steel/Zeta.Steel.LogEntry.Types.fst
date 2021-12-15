module Zeta.Steel.LogEntry.Types
open Zeta.Steel.ApplicationTypes

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
  ebytes: Ghost.erased (Seq.seq U8.t)
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

let payload = either (key & mval_value) uninterpreted

type value = 
  | MValue of mval_value
  | DValue of option value_type

let record = key & value

open Zeta.Steel.Parser

let dummy_record : record = (InternalKey ({k = {v3 = 0uL; v2 = 0uL; v1 = 0uL; v0 = 0uL}; significant_digits = 0us }), DValue None)

let related (p:payload) (r:record) (relate: bool) =
  match p with
  | Inl (k, v) -> r == (k, MValue v)
  | Inr u ->
    if relate then
    match (spec_parse_pair spec_parser_key spec_parser_value) u.ebytes with
    | None -> False
    | Some ((k,v), n) -> n == U32.v u.len /\ (ApplicationKey k, DValue (Some v)) == r
    else r == dummy_record

noeq
type log_entry0 (relate: Ghost.erased bool) =
  | AddM : s:slot_id ->
           s':slot_id ->
           p:Ghost.erased payload ->
           r:record { related p r relate } ->
           log_entry0 relate

  | AddB : s:slot_id ->
           ts:timestamp ->
           tid:thread_id ->
           p:Ghost.erased payload ->
           r:record { related p r relate } ->
           log_entry0 relate

  | RunApp of runApp_payload
  | EvictM of evictM_payload
  | EvictB of evictB_payload
  | EvictBM of evictBM_payload
  | NextEpoch
  | VerifyEpoch

let log_entry = log_entry0 true
