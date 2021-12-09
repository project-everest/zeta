module Zeta.Formats.Pure
module LP = LowParse.Spec.Base

let serialize_length x =
  Zeta.Formats.EverParse.Value.value_size32 x

let parsed s v =
  LP.parse Zeta.Formats.EverParse.Vlog_entry.vlog_entry_parser s == Some (v, Seq.length s)

let serialize_stamped_record_spec r =
  let s = Zeta.Formats.EverParse.Stamped_record.stamped_record_serializer in
  LP.serialize_length s r;
  s r

let serialize_stamped_record_injective r1 r2 =
  LP.serializer_injective _ Zeta.Formats.EverParse.Stamped_record.stamped_record_serializer r1 r2
