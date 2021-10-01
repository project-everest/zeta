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
module A = Steel.Array
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

val create (ha:HA.ha)
  : Steel prf_set_hash
    (HA.ha_inv ha)
    (fun p -> prf_set_hash_inv p)
    (requires fun h0 ->
       HA.hash_value_of ha h0 == HA.initial_hash)
    (ensures fun _ p h1 -> v_hash p h1 == HA.initial_hash)

val free (p:prf_set_hash)
  : Steel HA.ha
    (prf_set_hash_inv p)
    (fun x -> HA.ha_inv x)
    (fun _ -> True)
    (fun h0 x h1 ->
      v_hash p h0 ==
      HA.hash_value_of x h1)

let maybe_update_hash_value (b:bool)
                            (ha:HA.hash_value_t)
                            (r:T.record)
                            (t:T.timestamp)
                            (tid:T.thread_id)
  : GTot HA.hash_value_t
  = if b
    then VM.update_hash_value ha r t tid
    else ha

val prf_update_hash (p:prf_set_hash)
                    (r:T.record)
                    (t:T.timestamp)
                    (thread_id:T.thread_id)
  : Steel bool
    (prf_set_hash_inv p)
    (fun _ -> prf_set_hash_inv p)
    (requires fun _ -> True)
    (ensures fun h0 b h1 ->
      v_hash p h1 ==
      maybe_update_hash_value b (v_hash p h0) r t thread_id)
