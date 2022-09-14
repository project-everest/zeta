module Zeta.Steel.ExternalPtr

// DO NOT FRIEND this module!

module A = Steel.ST.Array
module U32 = FStar.UInt32
module U8 = FStar.UInt8

inline_for_extraction
val extern_ptr : Type0

val gtake (p: extern_ptr) : GTot (A.array U8.t)

inline_for_extraction
val valid (p: extern_ptr) (n: U32.t) : Pure bool
  (requires True)
  (ensures (fun b -> b == true ==> U32.v n == A.length (gtake p)))

inline_for_extraction
val take (p: extern_ptr) (n: Ghost.erased U32.t) : Pure (A.array U8.t)
  (requires (valid p n))
  (ensures (fun y -> y == gtake p))
