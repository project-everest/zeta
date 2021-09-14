module Veritas.Steel.PRFSetHash

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
open Steel.Array
open FStar.Ghost
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module T = Veritas.Formats.Types
module VM = Veritas.Steel.VerifierModel
module AT = Steel.Effect.Atomic
module VFT = Veritas.Formats.Types
module A = Veritas.Steel.Array
module HA = Veritas.Steel.HashAccumulator

val prf_set_hash
  : Type0

val prf_set_hash_sl (_:prf_set_hash)
  : slprop u#1

val prf_set_hash_repr
  : Type0

val hash_value_of (p:prf_set_hash_repr)
  : HA.hash_value_t

val prf_set_hash_sel (r:prf_set_hash)
  : GTot (selector prf_set_hash_repr (prf_set_hash_sl r))

[@@__steel_reduce__]
noextract
let prf_set_hash_inv' (r:prf_set_hash)
  : GTot vprop'
  = { hp = prf_set_hash_sl r;
      t = prf_set_hash_repr;
      sel = prf_set_hash_sel r}

unfold
let prf_set_hash_inv (r:prf_set_hash)
  : vprop
  = VUnit (prf_set_hash_inv' r)

[@@ __steel_reduce__]
let v_hash (#p:vprop)
           (r:prf_set_hash)
           (h:rmem p{FStar.Tactics.with_tactic selector_tactic
                      (can_be_split p (prf_set_hash_inv r) /\ True)})
  : GTot HA.hash_value_t
  = hash_value_of (h (prf_set_hash_inv r))

val create (_:unit)
  : Steel prf_set_hash
    emp
    (fun p -> prf_set_hash_inv p)
    (requires fun _ -> True)
    (ensures fun _ p h1 -> v_hash p h1 == HA.initial_hash)

val free (p:prf_set_hash)
  : SteelT unit
    (prf_set_hash_inv p)
    (fun _ -> emp)

val prf_update_hash (p:prf_set_hash)
                    (r:T.record)
                    (t:T.timestamp)
                    (thread_id:T.thread_id)
  : Steel unit
    (prf_set_hash_inv p)
    (fun _ -> prf_set_hash_inv p)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      v_hash p h1 == VM.update_hash_value (v_hash p h0) r t thread_id)

val prf_read_hash (p:prf_set_hash) (out:A.array U8.t)
  : Steel unit
    (prf_set_hash_inv p `star` A.varray out)
    (fun _ -> prf_set_hash_inv p `star` A.varray out)
    (requires fun _ -> A.length out == 32)
    (ensures fun h0 _ h1 ->
      A.length out == 32 /\
      v_hash p h0 == v_hash p h1 /\
      A.asel out h1 == v_hash p h1)

val prf_hash_agg (a0 a1:A.array U8.t)
  : Steel unit
    (A.varray a0 `star` A.varray a1)
    (fun _ -> A.varray a0 `star` A.varray a1)
    (requires fun _ ->
      A.length a0 == 32 /\
      A.length a1 == 32)
    (ensures fun h0 _ h1 ->
      A.length a0 == 32 /\
      A.length a1 == 32 /\
      A.asel a1 h0 == A.asel a1 h1 /\
      A.asel a0 h1 ==
        HA.aggregate_hash_value (A.asel a0 h0) (A.asel a1 h0))
