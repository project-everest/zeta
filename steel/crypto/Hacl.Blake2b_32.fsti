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
module A = Steel.ST.Array

open Steel.ST.Util

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
  -> #sout:Ghost.erased (Seq.seq U8.t)
  -> output: A.array U8.t
  -> ll: size_t
  -> #p:perm
  -> #sd:Ghost.erased (Seq.seq U8.t)
  -> d: A.array U8.t { U32.v ll <= Seq.length sd }
  -> ST unit
  (A.pts_to output full_perm sout `star` A.pts_to d p sd)
  (fun _ -> A.pts_to output full_perm
                  (spec (Seq.slice sd 0 (U32.v ll))
                        0
                        Seq.empty
                        (UInt32.v nn))
         `star`
         A.pts_to d p sd)
  (requires
    A.length d >= U32.v ll /\
    A.length output = U32.v nn)
  (ensures fun _ ->
    True)
