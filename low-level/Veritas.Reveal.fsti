module Veritas.Reveal

val reveal_u8: unit -> Lemma (ensures Lib.IntTypes.uint8 == FStar.UInt8.t)
