module Zeta.LowStar.LogEntry
open Zeta.Steel.LogEntry.Spec
open Zeta.LowStar.Parser

val zeta__parser_log_entry : parser spec_parser_log_entry

val zeta__serialize_stamped_record : serializer spec_serializer_stamped_record

val zeta__serialize_value : serializer spec_serializer_value

val zeta__parser_u256 : parser spec_parser_u256
