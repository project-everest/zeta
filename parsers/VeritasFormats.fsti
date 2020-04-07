module VeritasFormats

module LP = LowParse.SLow.Base

val parse_entry_kind : (k: LP.parser_kind { k.LP.parser_kind_subkind == Some LP.ParserStrong })

val parse_entry_spec : LP.parser parse_entry_kind Veritas.SparseMerkleVerifier.verifier_log_entry

val serialize_entry_spec : LP.serializer parse_entry_spec

val parse_entry : LP.parser32 parse_entry_spec

val serialize_entry : LP.serializer32 serialize_entry_spec
