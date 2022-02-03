module Zeta.Steel.LogEntry
include Zeta.Steel.LogEntry.Spec
open Zeta.Steel.Parser
module U32 = FStar.UInt32

val parser_log_entry : parser spec_parser_log_entry
