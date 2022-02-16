module Zeta.Steel.LogEntry
include Zeta.Steel.LogEntry.Spec
open Zeta.Steel.Parser
module U32 = FStar.UInt32

val parser_log_entry : parser spec_parser_log_entry

val serialize_stamped_record : serializer spec_serializer_stamped_record

val serialize_value : serializer spec_serializer_value
