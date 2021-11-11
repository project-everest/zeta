module Zeta.Steel.VerifierTypes

open FStar.Ghost
open Zeta.Steel.ApplicationTypes
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
open Zeta.Steel.FormatsManual
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
open Steel.Array

module T = Zeta.Steel.FormatsManual
module M = Zeta.Steel.ThreadStateModel
module A = Steel.Array
module AEH = Zeta.Steel.AggregateEpochHashes

#push-options "--ide_id_info_off"

val thread_state_t
  : Type0

noextract
val thread_state_inv (t:thread_state_t)
  : vprop

val type_of_thread_state_inv (t:thread_state_t) :
  Lemma (ensures (t_of (thread_state_inv t)) == M.thread_state_model)
        [SMTPat (t_of (thread_state_inv t))]

let coerce_eq (#a:Type) (#b:Type) (_:squash (a == b)) (x:a) : b = x
let value_of (t:thread_state_t) ($r:rmem (thread_state_inv t))
  : GTot M.thread_state_model
  = type_of_thread_state_inv t;
    coerce_eq () (r (thread_state_inv t))

val elim_thread_state_inv (#o:_) (t:thread_state_t)
  : SteelGhost unit o
    (thread_state_inv t)
    (fun _ -> thread_state_inv t)
    (requires fun h0 -> True)
    (ensures fun h0 _ h1 ->
      let tsm0 = value_of t h0 in
      let tsm1 = value_of t h1 in
      tsm0 == tsm1 /\
      tsm1 == M.verify_model (M.init_thread_state_model tsm1.thread_id)
                             tsm1.processed_entries)
