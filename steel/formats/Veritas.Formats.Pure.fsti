module Veritas.Formats.Pure
include Veritas.Formats.Aux
include Veritas.Formats.Types

module U32 = FStar.UInt32

val serialize_length : value -> (l: U32.t { U32.v l > 0 })
