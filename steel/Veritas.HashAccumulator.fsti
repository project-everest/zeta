module Veritas.HashAccumulator
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module A = Steel.Array

open Steel.Effect.Common
open Steel.Effect
open Steel.Reference

inline_for_extraction noextract
let blake2_max_input_length = pow2 32 - 1 - 128

// NOTE: we do not have an agile spec for the keyed hash functionality :(, so
// we're making Blake2-dependent assumptions without corresponding agile predicates
noextract inline_for_extraction
let hashable_bytes = s:Seq.seq U8.t { Seq.length s <= blake2_max_input_length }
let hashable_buffer = b:A.array U8.t { A.length b <= blake2_max_input_length }

let hash_value_t = Seq.lseq U8.t 32

val initial_hash
  : hash_value_t

val hash_value (_:hashable_bytes)
  : hash_value_t

val aggregate_hash_value (_ _: hash_value_t)
  : hash_value_t

let hash_value_buf = b:A.array U8.t{ A.length b == 32 }

[@@ __steel_reduce__]
let as_hash_value (#p:vprop) (r:hash_value_buf)
    (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (A.varray r) /\ True)})
  = A.asel r h

val state : Type0

val invariant (s: state) : vprop

val v_hash
     (#p:vprop)
     (t:state)
     (h:rmem p{
       FStar.Tactics.with_tactic
         selector_tactic
         (can_be_split p (invariant t) /\ True)
     })
  : hash_value_t


(*** THE MAIN INTERFACE ***)

(** Create an instance of a hash accumulator in the heap *)
val create_in (_:unit)
  : Steel state
    emp
    (fun s -> invariant s)
    (requires fun _ -> True)
    (ensures fun _ s h1 ->
       v_hash s h1 == initial_hash)

(** Combine two hash values held in b1 and b2 into b1 *)
val aggregate_hash_value_buf (b1: hash_value_buf) (b2: hash_value_buf)
  : Steel unit
    (A.varray b1 `star` A.varray b2)
    (fun _ -> A.varray b1 `star` A.varray b2)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      as_hash_value b2 h0 == as_hash_value b2 h1 /\
      as_hash_value b1 h1 == aggregate_hash_value (as_hash_value b1 h0)
                                                  (as_hash_value b2 h0))

(** Hash the (input[0, l)) into the hash accumulate s *)
val add (s:state) (input:hashable_buffer) (l:U32.t)
  : Steel unit
    (invariant s `star` A.varray input)
    (fun _ -> invariant s `star` A.varray input)
    (requires fun h0 ->
      U32.v l <= A.length input)
    (ensures fun h0 _ h1 ->
      U32.v l <= A.length input /\
      v_hash s h1 ==
      aggregate_hash_value (v_hash s h0)
                           (hash_value (Seq.slice (A.asel input h0) 0 (U32.v l))))

(** Read the current value of the hash into out *)
val get (s:state) (out:hash_value_buf)
  : Steel unit
    (invariant s `star` A.varray out)
    (fun _ -> invariant s `star` A.varray out)
    (requires fun h0 -> True)
    (ensures fun h0 r h1 ->
      v_hash s h0 == as_hash_value out h1)

(** Free the hash accumulator *)
val free (s:state)
  : SteelT unit
    (invariant s)
    (fun _ -> emp)
