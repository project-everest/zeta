module Zeta.Steel.LogEntry
open Zeta.Steel.ApplicationTypes
open Zeta.Steel.FormatsManual
module M = Zeta.Steel.ThreadStateModel
open Zeta.Steel.Parser
module U32 = FStar.UInt32
open FStar.Ghost

assume
val spec_parse_pair (p0:spec_parser 'a) (p1:spec_parser 'b)
  : spec_parser ('a & 'b)

let related (p:M.payload) (r:record) =
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
           p:erased M.payload ->
           r:record { related p r } ->
           log_entry

  | AddB : s:slot_id ->
           ts:timestamp ->
           tid:thread_id ->
           p:erased M.payload ->
           r:record { related p r } ->
           log_entry

  | RunApp of runApp_payload
  | EvictM of evictM_payload
  | EvictB of evictB_payload
  | EvictBM of evictBM_payload
  | NextEpoch
  | VerifyEpoch

assume
val spec_parser_log_entry : spec_parser log_entry

// I will use this in the implementation of verifier
assume
val parser_log_entry : parser spec_parser_log_entry

// But, I want to specify the verifier in terms of log_entry_base
// So, I also want something like this

assume
val log_entry_base_of_log_entry (l:log_entry) : GTot log_entry_base //injective

assume
val spec_parse_map (p0:spec_parser 'a) (p1:'a -> GTot 'b)
  : spec_parser 'b

let spec_parser_log_entry_base
  : spec_parser log_entry_base
  = spec_parse_map spec_parser_log_entry log_entry_base_of_log_entry
