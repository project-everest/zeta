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
  st           : vstore;  //a map from keys (cache ids) to merkle leaf or internal nodes
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
      model_failed = sel t.failed (focus_rmem h (thread_state_inv t));
      model_store = asel t.st (focus_rmem h (thread_state_inv t));
      model_clock = sel t.clock (focus_rmem h (thread_state_inv t));
      model_hadd = PRF.v_hash t.hadd (focus_rmem h (thread_state_inv t));
      model_hevict = PRF.v_hash t.hevict (focus_rmem h (thread_state_inv t))
    }

// AF: Requires some integers reasoningm, but should be straightforward
val update_clock (ts:T.timestamp) (vs:thread_state_t)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 -> v_thread vs h1 == model_update_clock (v_thread vs h0) ts)

val fail (vs:thread_state_t) (msg:string)
  : SteelF unit
             (thread_state_inv vs)
             (fun _ -> thread_state_inv vs)
             (requires fun _ -> True)
             (ensures fun h0 _ h1 -> v_thread vs h1 == model_fail (v_thread vs h0))


val vget (s:U16.t) (k:T.key) (v:T.data_value) (vs: thread_state_t)
  : Steel unit
          (thread_state_inv vs)
          (fun _ -> thread_state_inv vs)
          (requires fun h -> U16.v s < length (v_thread vs h).model_store)
          (ensures fun h0 _ h1 ->
            U16.v s < length (v_thread vs h0).model_store /\
            v_thread vs h1 == vget_model (v_thread vs h0) s k v
          )

val vput (s:U16.t) (k:T.key) (v:T.data_value) (vs: thread_state_t)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h -> U16.v s < length (v_thread vs h).model_store)
    (ensures fun h0 _ h1 ->
      U16.v s < length (v_thread vs h0).model_store /\
      v_thread vs h1 == vput_model (v_thread vs h0) s k v)

val vaddm (s:U16.t) (r:T.record) (s':U16.t) (vs:_)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h0 ->
      U16.v s  < length (v_thread vs h0).model_store /\
      U16.v s' < length (v_thread vs h0).model_store)
    (ensures fun h0 _ h1 ->
      U16.v s  < length (v_thread vs h0).model_store /\
      U16.v s' < length (v_thread vs h0).model_store /\
      v_thread vs h1 == vaddm_model (v_thread vs h0) s r s')

val vevictm (s s':U16.t) (vs:_)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h0 ->
      U16.v s  < length (v_thread vs h0).model_store /\
      U16.v s' < length (v_thread vs h0).model_store)
    (ensures fun h0 _ h1 ->
      U16.v s  < length (v_thread vs h0).model_store /\
      U16.v s' < length (v_thread vs h0).model_store /\
      v_thread vs h1 == vevictm_model (v_thread vs h0) s s')

val vaddb (s:U16.t)
          (r:T.record)
          (t:T.timestamp)
          (thread_id:T.thread_id)
          (vs:thread_state_t)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h -> U16.v s < length (v_thread vs h).model_store)
    (ensures fun h0 _ h1 ->
      U16.v s < length (v_thread vs h0).model_store /\
      v_thread vs h1 == vaddb_model (v_thread vs h0) s r t thread_id)

val vevictb (s:U16.t)
            (t:T.timestamp)
            (vs:thread_state_t)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h -> U16.v s < length (v_thread vs h).model_store)
    (ensures  fun h0 _ h1 ->
      U16.v s < length (v_thread vs h0).model_store /\
      v_thread vs h1 == vevictb_model (v_thread vs h0) s t)

val vevictbm (s s':U16.t)
             (t:T.timestamp)
             (vs:_)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (fun h0 ->
      U16.v s < length (v_thread vs h0).model_store /\
      U16.v s' < length (v_thread vs h0).model_store)
    (fun h0 _ h1 ->
      U16.v s < length (v_thread vs h0).model_store /\
      U16.v s' < length (v_thread vs h0).model_store /\
      v_thread vs h1 == vevictbm_model (v_thread vs h0) s s' t)
