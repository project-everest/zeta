module Veritas.Steel.Verifier

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
open Steel.Array
open FStar.Ghost
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module T = Veritas.Formats.Types

open Veritas.Steel.VCache
open Veritas.Steel.VerifierModel
open Veritas.ThreadStateModel
module PRF = Veritas.Steel.PRFSetHash
module L = Veritas.Steel.Log
module U8 = FStar.UInt8
module A = Steel.Array

val thread_state_t
  : Type0

noextract
val thread_state_inv (t:thread_state_t)
  : vprop

val v_thread
     (#p:vprop)
     (t:thread_state_t)
     (h:rmem p{
       FStar.Tactics.with_tactic
         selector_tactic
         (can_be_split p (thread_state_inv t) /\ True)
     })
  : thread_state_model

let verify_array_post (a:A.array U8.t)
                      (tsm0:thread_state_model)
                      (sopt:option L.repr)
                      (tsm1:thread_state_model)
  = match sopt with
    | None -> tsm1.model_failed == true
    | Some s ->
        exists (l:L.log).{:pattern (Log.parsed_log_inv l s)}
          L.log_array l == a /\
          Log.parsed_log_inv l s /\
          tsm1 == verify_model tsm0 s

val verify_array (vs:_)
                 (len:U32.t)
                 (a:A.array U8.t)
  : Steel (option L.repr)
    (thread_state_inv vs `star` A.varray a)
    (fun _ -> thread_state_inv vs `star` A.varray a)
    (requires fun _ ->
      U32.v len == A.length a)
    (ensures fun h0 sopt h1 ->
      verify_array_post a (v_thread vs h0) sopt (v_thread vs h1))

val create (tid:T.thread_id) (store_size:U16.t)
  : Steel thread_state_t
    emp
    (fun vs -> thread_state_inv vs)
    (requires fun _ -> True)
    (ensures fun _ vs h1 ->
      v_thread vs h1 == init_thread_state_model tid store_size)

val free (vs:thread_state_t)
  : SteelT unit
    (thread_state_inv vs)
    (fun _ -> emp)
