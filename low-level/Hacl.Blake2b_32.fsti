module Hacl.Blake2b_32

// This file is here to prevent depending on the actual HACL* repository.
// The signatures do not correspond to the ones found in the original HACL* file.
// We assume verification good nonetheless and reconcile these files at link-time.
//
// In the future, we hope that the hacl-star repository will provided a minimal
// set of fstis that allow bringing into scope the signatures (only) of the
// various API functions of EverCrypt, all specified in terms of abstract
// specifications.

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST

#set-options "--fuel 0 --ifuel 0"

// NB: this is not the definition from HACL*, since it does not rely on secret integers
inline_for_extraction noextract
let bytes = Seq.seq UInt8.t

inline_for_extraction noextract
let lbytes l = s:Seq.seq UInt8.t { Seq.length s = l }

inline_for_extraction noextract
let size_nat = n:nat { n <= pow2 32 - 1 }

open FStar.Mul

inline_for_extraction noextract
let size_block = 128

noextract
val spec:
    d:bytes
  -> kk:size_nat{kk <= 64 /\ (if kk = 0 then Seq.length d < pow2 128 else Seq.length d + 128 < pow2 64)}
  -> k:lbytes kk
  -> nn:size_nat{1 <= nn /\ nn <= 64} ->
  Tot (lbytes nn)

inline_for_extraction noextract
let size_t = UInt32.t

inline_for_extraction noextract
let max_output = 64

inline_for_extraction noextract
let max_key = 64

inline_for_extraction noextract
let lbuffer t l = b:B.buffer t { B.len b == l }

val blake2b:
    nn:size_t{1 <= UInt32.v nn /\ UInt32.v nn <= max_output}
  -> output: lbuffer UInt8.t nn
  -> ll: size_t
  -> d: lbuffer UInt8.t ll
  -> kk: size_t{UInt32.v kk <= max_key}
  -> k: lbuffer UInt8.t kk ->
  ST.Stack unit
    (requires (fun h ->
      let open B in
      live h output /\ live h d /\ live h k
      /\ disjoint output d /\ disjoint output k /\ disjoint d k))
    (ensures  (fun h0 _ h1 ->
      B.modifies (B.loc_buffer output) h0 h1
      /\ B.as_seq h1 output == spec (B.as_seq h0 d) (UInt32.v kk) (B.as_seq h0 k) (UInt32.v nn)))
