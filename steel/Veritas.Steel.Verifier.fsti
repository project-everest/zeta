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

let counter_t = ref U64.t

noeq
type thread_state_t = {
  id           : T.thread_id;
  len          : U16.t;
  st           : vstore len;  //a map from keys (cache ids) to merkle leaf or internal nodes
  clock        : counter_t;
  hadd         : PRF.prf_set_hash; //current incremental set hash values; TODO
  hevict       : PRF.prf_set_hash;
  failed       : ref bool
}

[@@__reduce__; __steel_reduce__]
noextract
let thread_state_inv (t:thread_state_t) : vprop =
  is_vstore t.st `star`
  vptr t.clock `star`
  vptr t.failed `star`
  PRF.prf_set_hash_inv t.hadd `star`
  PRF.prf_set_hash_inv t.hevict

[@@ __steel_reduce__]
unfold
let v_thread (#p:vprop) (t:thread_state_t)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (thread_state_inv t) /\ True)})
  : GTot thread_state_model
  = {
      model_thread_id = t.id;
      model_store_len = t.len;
      model_failed = sel t.failed (focus_rmem h (thread_state_inv t));
      model_store = asel t.st (focus_rmem h (thread_state_inv t));
      model_clock = sel t.clock (focus_rmem h (thread_state_inv t));
      model_hadd = PRF.v_hash t.hadd (focus_rmem h (thread_state_inv t));
      model_hevict = PRF.v_hash t.hevict (focus_rmem h (thread_state_inv t))
    }

val vget (vs: thread_state_t) (s:slot vs.len) (k:T.key) (v:T.data_value)
  : Steel unit
          (thread_state_inv vs)
          (fun _ -> thread_state_inv vs)
          (requires fun h -> True)
          (ensures fun h0 _ h1 ->
            v_thread vs h1 == vget_model (v_thread vs h0) s k v
          )

val vput (vs: thread_state_t) (s:slot vs.len) (k:T.key) (v:T.data_value)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h -> True)
    (ensures fun h0 _ h1 ->
      v_thread vs h1 == vput_model (v_thread vs h0) s k v)

val vaddm (vs:_) (s:slot vs.len) (r:T.record) (s':slot vs.len)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h0 -> True)
    (ensures fun h0 _ h1 ->
      v_thread vs h1 == vaddm_model (v_thread vs h0) s r s')

val vevictm (vs:_) (s s':slot vs.len)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h0 -> True)
    (ensures fun h0 _ h1 ->
      v_thread vs h1 == vevictm_model (v_thread vs h0) s s')

val vaddb (vs:thread_state_t)
          (s:slot vs.len)
          (r:T.record)
          (t:T.timestamp)
          (thread_id:T.thread_id)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h -> True)
    (ensures fun h0 _ h1 ->
      v_thread vs h1 == vaddb_model (v_thread vs h0) s r t thread_id)

val vevictb (vs:thread_state_t)
            (s:slot vs.len)
            (t:T.timestamp)

  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h -> True)
    (ensures  fun h0 _ h1 ->
      v_thread vs h1 == vevictb_model (v_thread vs h0) s t)

val vevictbm (vs:_)
             (s s':slot vs.len)
             (t:T.timestamp)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (fun h0 -> True)
    (fun h0 _ h1 ->
      v_thread vs h1 == vevictbm_model (v_thread vs h0) s s' t)
