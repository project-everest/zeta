module Veritas.Formats.Pure
module LP = LowParse.Spec.Base

let serialize_length x =
  Veritas.Formats.EverParse.Value.value_size32 x
