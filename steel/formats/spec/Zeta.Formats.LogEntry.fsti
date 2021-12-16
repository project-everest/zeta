module Zeta.Formats.LogEntry

module LP = LowParse.Spec.Base

val parse_log_entry_kind: (k: LP.parser_kind { k.LP.parser_kind_subkind == Some LP.ParserStrong })

val parse_log_entry (relate_payload: bool) : Tot (LP.parser parse_log_entry_kind (Zeta.Steel.LogEntry.Types.log_entry0 relate_payload))

val serialize_log_entry (relate_payload: bool) : Tot (LP.serializer (parse_log_entry relate_payload))

