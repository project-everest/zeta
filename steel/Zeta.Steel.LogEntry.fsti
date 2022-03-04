module Zeta.Steel.LogEntry
include Zeta.Steel.LogEntry.Spec
open Zeta.Steel.Parser
module U32 = FStar.UInt32

val zeta__parser_log_entry : parser spec_parser_log_entry

inline_for_extraction
noextract
let parser_log_entry : parser spec_parser_log_entry = zeta__parser_log_entry

val zeta__serialize_stamped_record : serializer spec_serializer_stamped_record

inline_for_extraction
noextract
let serialize_stamped_record : serializer spec_serializer_stamped_record = zeta__serialize_stamped_record

inline_for_extraction
noextract
val zeta__serialize_value : serializer spec_serializer_value

inline_for_extraction
noextract
let serialize_value : serializer spec_serializer_value = zeta__serialize_value

val zeta__parser_u256 : parser spec_parser_u256

inline_for_extraction
noextract
let parser_u256 : parser spec_parser_u256 = zeta__parser_u256
