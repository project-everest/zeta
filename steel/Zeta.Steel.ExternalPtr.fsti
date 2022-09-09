module Zeta.Steel.ExternalPtr

// DO NOT FRIEND this module!

module A = Steel.ST.Array
module U32 = FStar.UInt32

inline_for_extraction
val extern_ptr (a: Type0) : Type0

val gtake (#a: Type) (p: extern_ptr a) : GTot (A.array a)

inline_for_extraction
val valid (#a: Type) (p: extern_ptr a) (n: U32.t) : Pure bool
  (requires True)
  (ensures (fun b -> b == true ==> U32.v n == A.length (gtake p)))

inline_for_extraction
val take (#a: Type) (p: extern_ptr a) (n: Ghost.erased U32.t) : Pure (A.array a)
  (requires (valid p n))
  (ensures (fun y -> y == gtake p))
