module Hacl.Hash.SHA2

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
let max_input_length = pow2 61 - 1

inline_for_extraction noextract
let hash_length = 32

noextract
val spec (input:bytes{Seq.length input <= max_input_length}):
  Tot (s:bytes { Seq.length s = hash_length })

val hash_256:
  input:B.buffer UInt8.t ->
  input_len:UInt32.t { B.length input = UInt32.v input_len } ->
  dst:B.buffer UInt8.t { B.length dst == hash_length } ->
  ST.Stack unit
    (requires (fun h ->
      B.live h input /\
      B.live h dst /\
      B.disjoint input dst /\
      B.length input <= max_input_length))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer dst) h0 h1) /\
      Seq.equal (B.as_seq h1 dst) (spec (B.as_seq h0 input))))

