module Veritas.External

module B = FStar.Bytes

// This interface could be potentially refined with a function specification if
// we wish to take a dependency on HACL* specifications.
val sha2_256: b:B.bytes { B.length b <= pow2 32 - 1 } -> b:B.bytes { B.length b = 256 }
