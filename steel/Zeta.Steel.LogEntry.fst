module Zeta.Steel.LogEntry
include Zeta.Steel.LogEntry.Types
open Zeta.Steel.ApplicationTypes
open Zeta.Steel.Parser
// open Zeta.Steel.FormatsManual
module U32 = FStar.UInt32
open FStar.Ghost

assume
val spec_parser_log_entry : spec_parser log_entry

// I will use this in the implementation of verifier
assume
val parser_log_entry : parser spec_parser_log_entry

(*
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
*)
