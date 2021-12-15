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

let payload = either (key & mval_value) uninterpreted

type value = 
  | MValue of mval_value
  | DValue of option value_type

let record = key & value

open Zeta.Steel.Parser
assume
val spec_parse_pair (p0:spec_parser 'a) (p1:spec_parser 'b)
  : spec_parser ('a & 'b)


let related (p:payload) (r:record) =
  match p with
  | Inl (k, v) -> r == (k, MValue v)
  | Inr u ->
    match (spec_parse_pair spec_parser_key spec_parser_value) u.ebytes with
    | None -> False
    | Some ((k,v), n) -> n == U32.v u.len /\ (ApplicationKey k, DValue (Some v)) == r

noeq
type log_entry =
  | AddM : s:slot_id ->
           s':slot_id ->
           p:Ghost.erased payload ->
           r:record { related p r } ->
           log_entry

  | AddB : s:slot_id ->
           ts:timestamp ->
           tid:thread_id ->
           p:Ghost.erased payload ->
           r:record { related p r } ->
           log_entry

  | RunApp of runApp_payload
  | EvictM of evictM_payload
  | EvictB of evictB_payload
  | EvictBM of evictBM_payload
  | NextEpoch
  | VerifyEpoch
