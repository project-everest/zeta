module Veritas.Formats.Pure
include Veritas.Formats.Aux
include Veritas.Formats.Types

module U32 = FStar.UInt32
module U8 = FStar.UInt8

val serialize_length : value -> (l: U32.t { U32.v l > 0 })

val parsed: Seq.seq U8.t -> vlog_entry -> prop
