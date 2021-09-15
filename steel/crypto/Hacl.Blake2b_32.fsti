module Hacl.Blake2b_32

// This file is here to prevent depending on the actual HACL*
// repository.  The signatures do not correspond to the ones found in
// the original HACL* file. Notably, this is a Steel signature,
// whereas HACL* is verified in Low*

// We assume verification good nonetheless and reconcile these files
// at link-time.

// In the future, we hope that the hacl-star repository will provided
// a minimal set of fstis that allow bringing into scope the
// signatures (only) of the various API functions of EverCrypt, all
// specified in terms of abstract specifications.

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module A = Steel.Array

open Steel.Effect.Common
open Steel.Effect

inline_for_extraction noextract
let size_nat = n:nat { n <= pow2 32 - 1 }
let size_t = U32.t
let max_output = 64
let bytes = Seq.seq U8.t

inline_for_extraction noextract
let lbytes l = s:bytes { Seq.length s = l }

noextract
val spec :
    d:bytes
  -> kk:size_nat{kk <= 64 /\ (if kk = 0 then Seq.length d < pow2 128 else Seq.length d + 128 < pow2 64)}
  -> k:lbytes kk
  -> nn:size_nat{1 <= nn /\ nn <= 64} ->
  Tot (lbytes nn)

val blake2b:
    nn:size_t{1 <= UInt32.v nn /\ UInt32.v nn <= max_output}
  -> output: A.array U8.t
  -> ll: size_t
  -> d: A.array U8.t
  -> Steel unit
  (A.varray output `star` A.varray d)
  (fun _ -> A.varray output `star` A.varray d)
  (requires fun _ ->
    A.length d >= U32.v ll /\
    A.length output = U32.v nn)
  (ensures fun h0 _ h1 ->
    A.length d >= U32.v ll /\
    A.length output = U32.v nn /\
    A.asel d h0 == A.asel d h1 /\
    A.asel output h1 ==
      spec
        (Seq.slice (A.asel d h0) 0 (U32.v ll))
        0 Seq.empty (UInt32.v nn))
