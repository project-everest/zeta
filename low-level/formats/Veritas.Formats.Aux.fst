module Veritas.Formats.Aux

module U16 = FStar.UInt16

type significant_digits_t = significant_digits: U16.t { U16.v significant_digits <= 256 }
