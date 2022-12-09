module Hacl.Hash.Blake2b_256

// This file is here to prevent depending on the actual HACL*
// repository.  The signatures do not correspond to the ones found in
// the original HACL* file. Notably, this is a Steel signature,
// whereas HACL* is verified in Low*

// We take verification as good nonetheless and reconcile these files
// at link-time.

// In the future, we hope that the hacl-star repository will provided
// a minimal set of fstis that allow bringing into scope the
// signatures (only) of the various API functions of EverCrypt, all
// specified in terms of abstract specifications.

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module A = Steel.ST.Array
module R = Steel.ST.Reference
module SR = Steel.Reference
open Steel.ST.Util

inline_for_extraction noextract
let size_nat = n:nat { n <= pow2 32 - 1 }

let size_t = U32.t

let max_output = 64

let bytes = Seq.seq U8.t

let max_key_size = 64

inline_for_extraction noextract
let lbytes l = s:bytes { Seq.length s = l }

noextract
val spec :
    d:bytes
  -> kk:size_nat{kk <= 64 /\ (if kk = 0 then Seq.length d < pow2 128 else Seq.length d + 128 < pow2 64)}
  -> k:lbytes kk
  -> nn:size_nat{1 <= nn /\ nn <= 64} ->
  GTot (lbytes nn)
  
val blake2b 
    (#sout:Ghost.erased (Seq.seq U8.t))
    (#in_p:perm)
    (#in_v:Ghost.erased (Seq.seq U8.t))
    (nn:size_t{1 <= UInt32.v nn /\ UInt32.v nn <= max_output})
    (output: A.array U8.t)
    (ll: size_t)
    (input: A.array U8.t { U32.v ll <= Seq.length in_v })
    (kk: size_t { kk = 0ul })
    (key: SR.ref U8.t { key == SR.null })
 : ST unit
    (A.pts_to output full_perm sout `star`
     A.pts_to input in_p in_v)
    (fun _ -> 
      A.pts_to output full_perm
               (spec (Seq.slice in_v 0 (U32.v ll))
                     0 (Seq.create 0 0uy)
                     (UInt32.v nn)) `star`
      A.pts_to input in_p in_v)
  (requires
    A.length output = U32.v nn)
  (ensures fun _ ->
    True)
