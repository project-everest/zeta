module Veritas.Formats.Pure
module LP = LowParse.Spec.Base

let serialize_length x =
  Veritas.Formats.EverParse.Value.value_size32 x

let parsed s v =
  LP.parse Veritas.Formats.EverParse.Vlog_entry.vlog_entry_parser s == Some (v, Seq.length s)
