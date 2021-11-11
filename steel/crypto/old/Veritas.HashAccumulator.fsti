module Veritas.HashAccumulator

#set-options "--fuel 0 --ifuel 0"

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost
module S = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

open FStar.HyperStack.ST

// JP: not being agile over the hash algorithm for the moment, can be improved
// later; any keyed hash will do, HMAC would also work, AES-CMAC is the one
// currently used in Veritas

// Note: this restriction does not come from the spec but rather from the
// implementation. Is this really necessary? See discussion on Slack, could
// easily be 2 ^ 64 - 128.
inline_for_extraction noextract
let blake2_max_input_length = pow2 32 - 1 - 128

// NOTE: we do not have an agile spec for the keyed hash functionality :(, so
// we're making Blake2-dependent assumptions without corresponding agile predicates
noextract inline_for_extraction
let hashable_bytes = s:Seq.seq U8.t { Seq.length s <= blake2_max_input_length }
let hashable_buffer = b:B.buffer U8.t { B.length b <= blake2_max_input_length }

let hash_value_t = Seq.lseq U8.t 32

val initial_hash
  : hash_value_t

val hash_value (_:hashable_bytes)
  : hash_value_t

val aggregate_hash_value (_ _: hash_value_t)
  : hash_value_t

let hash_value_buf = B.lbuffer U8.t 32

let as_hash_value (b:hash_value_buf) (h:HS.mem)
  : GTot hash_value_t
  = B.as_seq h b

val state: Type0

val invariant (s: state) (h:HS.mem) : Type0

val v_hash (s:state) (h:HS.mem)
  : GTot hash_value_t

(** A bunch of infrastructure related to framing **)
val footprint (s: state): GTot B.loc

val frame: l:B.loc -> s:state -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant s h0 /\
    B.loc_disjoint l (footprint s) /\
    B.modifies l h0 h1))
  (ensures (
    invariant s h1 /\
    v_hash s h0 == v_hash s h1))

(*** THE MAIN INTERFACE ***)

(** Create an instance of a hash accumulator in the heap *)
val create_in: unit -> ST state
  (requires fun h0 -> True)
  (ensures fun h0 s h1 ->
    invariant s h1 /\
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint s) h0 h1 /\
    v_hash s h1 == initial_hash)

(** Combine two hash values held in b1 and b2 into b1 *)
val aggregate_hash_value_buf (b1: hash_value_buf) (b2: hash_value_buf)
  : Stack unit
    (requires fun h0 ->
      B.live h0 b1 /\
      B.live h0 b2 /\
      B.disjoint b1 b2)
    (ensures fun h0 _ h1 ->
      B.(modifies (loc_buffer b1) h0 h1) /\
      as_hash_value b1 h1 == aggregate_hash_value (as_hash_value b1 h0)
                                                  (as_hash_value b2 h0))

(** Hash the (input[0, l)) into the hash accumulate s *)
val add: s:state -> input:hashable_buffer -> l:U32.t -> Stack unit
  (requires fun h0 ->
    invariant s h0 /\
    B.live h0 input /\
    B.(loc_disjoint (loc_buffer input) (footprint s)) /\
    U32.v l <= U32.v (B.len input))
  (ensures fun h0 _ h1 ->
    invariant s h1 /\
    B.modifies (footprint s) h0 h1 /\
    v_hash s h1 ==
    aggregate_hash_value (v_hash s h0)
                         (hash_value (Seq.slice (B.as_seq h0 input) 0 (U32.v l))))

(** Read the current value of the hash into out *)
val get: s:state -> out:hash_value_buf -> Stack unit
  (requires fun h0 ->
    invariant s h0 /\
    B.live h0 out /\
    B.loc_disjoint (B.loc_buffer out) (footprint s))
  (ensures fun h0 r h1 ->
    invariant s h0 /\
    B.modifies (B.loc_buffer out) h0 h1 /\
    v_hash s h0 == as_hash_value out h1)

(** Free the hash accumulator *)
val free: s:state -> ST unit
  (requires fun h0 ->
    invariant s h0)
  (ensures (fun h0 _ h1 ->
    B.modifies (footprint s) h0 h1))
