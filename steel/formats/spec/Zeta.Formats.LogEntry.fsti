module Zeta.Formats.LogEntry

module LP = LowParse.Spec.Base

val parse_log_entry_kind: (k: LP.parser_kind { k.LP.parser_kind_subkind == Some LP.ParserStrong /\ k.LP.parser_kind_low >= 1 })

val parse_log_entry : LP.parser parse_log_entry_kind (Zeta.Steel.LogEntry.Types.log_entry)

val serialize_log_entry : LP.serializer parse_log_entry
