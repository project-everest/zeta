module Veritas.Steel.HashAccumulator
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module A = Steel.Array
open Steel.Memory
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

let hash_value_t = Seq.lseq U8.t 32 & nat

val ha
  : Type0

val ha_sl (_:ha)
  : slprop u#1

val ha_repr
  : Type0

val ha_sel (x:ha)
  : GTot (selector ha_repr (ha_sl x))

[@@__steel_reduce__]
noextract
let ha_inv' (x:ha)
  : GTot vprop'
  = { hp = ha_sl x;
      t = ha_repr;
      sel = ha_sel x}

unfold
let ha_inv (r:ha)
  : vprop
  = VUnit (ha_inv' r)
  
[@@ __steel_reduce__]
let repr_of (#p:vprop)
            (r:ha)
            (h:rmem p{FStar.Tactics.with_tactic selector_tactic
                      (can_be_split p (ha_inv r) /\ True)})
  : GTot ha_repr
  = h (ha_inv r)

val value_of (_:ha_repr)
  : hash_value_t
  
val initial_hash
  : hash_value_t

val hash_one_value (_:hashable_bytes)
  : hash_value_t

val aggregate_hashes (_ _: hash_value_t)
  : hash_value_t

[@@__steel_reduce__]
unfold
let hash_value_of (#p:vprop)
                  (r:ha)
                  (h:rmem p{FStar.Tactics.with_tactic selector_tactic
                            (can_be_split p (ha_inv r) /\ True)})
  : GTot hash_value_t
  = value_of (repr_of r h)


(*** THE MAIN INTERFACE ***)

(** Create an instance of a hash accumulator in the heap *)
val create (_:unit)
  : Steel ha
    emp
    (fun s -> ha_inv s)
    (requires fun _ -> True)
    (ensures fun _ s h1 ->
       hash_value_of s h1 == initial_hash)

(** Free the hash accumulator *)
val free (s:ha)
  : SteelT unit
    (ha_inv s)
    (fun _ -> emp)

//TODO: can't inline this if in the ensures of aggregate
let maybe_aggregate_hashes (b:bool) (h0 h1: hash_value_t) =
  if b then aggregate_hashes h0 h1
  else h0

val aggregate (b1 b2: ha)
  : Steel bool
    (ha_inv b1 `star` ha_inv b2)
    (fun _ -> ha_inv b1 `star` ha_inv b2)
    (requires fun _ -> True)
    (ensures fun h0 success h1 ->
      hash_value_of b2 h0 == hash_value_of b2 h1 /\
      hash_value_of b1 h1 ==
        maybe_aggregate_hashes success
          (hash_value_of b1 h0)
          (hash_value_of b2 h0))

val compare (b1 b2:ha)
  : Steel bool
    (ha_inv b1 `star` ha_inv b2)
    (fun _ -> ha_inv b1 `star` ha_inv b2)
    (requires fun _ -> True)
    (ensures fun h0 success h1 ->
      hash_value_of b1 h0 == hash_value_of b1 h1 /\
      hash_value_of b2 h0 == hash_value_of b2 h1 /\
      success = (hash_value_of b1 h1 = hash_value_of b2 h1))
  
(** Hash the (input[0, l)) into the hash accumulate s *)
val add (s:ha) (input:hashable_buffer) (l:U32.t)
  : Steel bool
    (ha_inv s `star` A.varray input)
    (fun _ -> ha_inv s `star` A.varray input)    
    (requires fun h0 ->
      U32.v l <= A.length input)
    (ensures fun h0 success h1 ->
      U32.v l <= A.length input /\    
      hash_value_of s h1 ==
        maybe_aggregate_hashes success
          (hash_value_of s h0)
          (hash_one_value (Seq.slice (A.asel input h0) 0 (U32.v l))))

(* An indexed variant of ha_inv *)
module AT = Steel.Effect.Atomic

val ha_val (r:ha) (v:Ghost.erased hash_value_t)
  : vprop

val ha_val_of_ha_inv (#o:_) (s:ha)
  : AT.SteelGhost (Ghost.erased hash_value_t) o
    (ha_inv s)
    (fun v -> ha_val s v)
    (requires fun _ -> True)
    (ensures fun h0 x _ -> 
       Ghost.reveal x == hash_value_of s h0)

val ha_inv_of_ha_val (#o:_) (#v:Ghost.erased hash_value_t) (s:ha)
  : AT.SteelGhost unit o
    (ha_val s v)
    (fun _ -> ha_inv s)
    (requires fun _ -> True)
    (ensures fun _ _ h1 ->
       hash_value_of s h1 == Ghost.reveal v)
