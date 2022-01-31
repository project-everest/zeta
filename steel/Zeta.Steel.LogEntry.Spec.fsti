module Zeta.Steel.LogEntry.Spec
include Zeta.Steel.LogEntry.Types
open Zeta.Steel.Parser

val spec_parser_log_entry : spec_parser log_entry
val spec_serializer_log_entry : spec_serializer spec_parser_log_entry
