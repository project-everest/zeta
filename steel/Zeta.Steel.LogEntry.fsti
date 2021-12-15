module Zeta.Steel.LogEntry
include Zeta.Steel.LogEntry.Types
open Zeta.Steel.Parser

val spec_parser_log_entry : spec_parser log_entry

val parser_log_entry : parser spec_parser_log_entry
