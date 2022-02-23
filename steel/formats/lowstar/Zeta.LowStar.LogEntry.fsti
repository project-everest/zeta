module Zeta.LowStar.LogEntry
open Zeta.Steel.LogEntry.Spec
open Zeta.LowStar.Parser

val parser_log_entry : parser spec_parser_log_entry

val serialize_stamped_record : serializer spec_serializer_stamped_record

val serialize_value : serializer spec_serializer_value

val parser_u256 : parser spec_parser_u256