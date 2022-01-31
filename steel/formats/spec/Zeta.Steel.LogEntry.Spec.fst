module Zeta.Steel.LogEntry.Spec

let spec_parser_log_entry = Zeta.Formats.LogEntry.parse_log_entry

let spec_serializer_log_entry x =
  assert (LowParse.Spec.Base.parse Zeta.Formats.LogEntry.parse_log_entry (Zeta.Formats.LogEntry.serialize_log_entry x) == Some (x, Seq.length (Zeta.Formats.LogEntry.serialize_log_entry x))); // pattern requires `LowParse.Spec.Base.parse`
  Zeta.Formats.LogEntry.serialize_log_entry x
