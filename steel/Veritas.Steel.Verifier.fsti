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

val prf_set_hash : Type0

// AF: Internally, should probably be implemented with a ghost reference to the model_hash
// The selector would then fetch the value in the ghost state
// The reason why we would need a ghost state is that the "spec" contains strictly more
// information than the concrete value. So we cannot reconstruct it out of just the concrete state
val prf_set_hash_sl (_:prf_set_hash) : slprop u#1
val prf_set_hash_sel (r:prf_set_hash) : selector (model_hash) (prf_set_hash_sl r)
[@@__steel_reduce__]
let prf_set_hash_inv' (r:prf_set_hash) : vprop' =
  { hp = prf_set_hash_sl r;
    t = model_hash;
    sel = prf_set_hash_sel r}
unfold
let prf_set_hash_inv (r:prf_set_hash) : vprop = VUnit (prf_set_hash_inv' r)

[@@ __steel_reduce__]
let v_hash (#p:vprop) (r:prf_set_hash)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (prf_set_hash_inv r) /\ True)})
  : GTot model_hash
  = h (prf_set_hash_inv r)

val prf_update_hash (p:prf_set_hash) (r:T.record) (t:T.timestamp) (thread_id:thread_id)
  : Steel unit
    (prf_set_hash_inv p)
    (fun _ -> prf_set_hash_inv p)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 -> v_hash p h1 == model_update_hash (v_hash p h0) r t thread_id)

let counter_t = ref U64.t

noeq
type thread_state_t = {
  id           : thread_id;
  st           : vstore;  //a map from keys (cache ids) to merkle leaf or internal nodes
  clock        : counter_t;
  hadd         : prf_set_hash; //current incremental set hash values; TODO
  hevict       : prf_set_hash;
  failed       : ref bool
}

[@@__reduce__; __steel_reduce__]
let thread_state_inv (t:thread_state_t) : vprop =
  is_vstore t.st `star`
  vptr t.clock `star`
  vptr t.failed `star`
  prf_set_hash_inv t.hadd `star`
  prf_set_hash_inv t.hevict

[@@ __steel_reduce__]
unfold
let v_thread (#p:vprop) (t:thread_state_t)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (thread_state_inv t) /\ True)})
  : GTot thread_state_model
  = {
      model_failed = sel t.failed (focus_rmem h (thread_state_inv t));
      model_store = asel t.st (focus_rmem h (thread_state_inv t));
      model_clock = sel t.clock (focus_rmem h (thread_state_inv t));
      model_hadd = v_hash t.hadd (focus_rmem h (thread_state_inv t));
      model_hevict = v_hash t.hevict (focus_rmem h (thread_state_inv t))
    }

// AF: Requires some integers reasoningm, but should be straightforward
val update_clock (ts:T.timestamp) (vs:thread_state_t)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 -> v_thread vs h1 == model_update_clock (v_thread vs h0) ts)


let fail (vs:thread_state_t) (msg:string)
  : SteelF unit
             (thread_state_inv vs)
             (fun _ -> thread_state_inv vs)
             (requires fun _ -> True)
             (ensures fun h0 _ h1 -> v_thread vs h1 == model_fail (v_thread vs h0))
  = write vs.failed false; ()

#push-options "--fuel 0 --ifuel 0"

let vget (s:U16.t) (v:T.value) (vs: thread_state_t)
  : Steel unit
          (thread_state_inv vs)
          (fun _ -> thread_state_inv vs)
          (requires fun h -> U16.v s < length (v_thread vs h).model_store)
          (ensures fun h0 _ h1 ->
            U16.v s < length (v_thread vs h0).model_store /\
            v_thread vs h1 == vget_model (v_thread vs h0) s v
          )
  = let ro = VCache.vcache_get_record vs.st s in
    match ro with
    | None ->
      fail vs "Slot not found"
    | Some r' ->
      if v = r'.T.record_value
      // AF: Usual problem of Steel vs SteelF difference between the two branches
      then (noop (); ())
      else fail vs "Failed: inconsistent key or value in Get"

(* verifier write operation *)
let vput (s:U16.t) (v:T.value) (vs: thread_state_t)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h -> U16.v s < length (v_thread vs h).model_store)
    (ensures fun h0 _ h1 ->
      U16.v s < length (v_thread vs h0).model_store /\
      v_thread vs h1 == vput_model (v_thread vs h0) s v)
  = let ro = VCache.vcache_get_record vs.st s in
    match ro with
    | None ->
      fail vs "Slot not found"

    | Some r ->
      vcache_update_record vs.st s ({ r with T.record_value = v });
      ()

let vaddb (s:U16.t)
          (r:T.record)
          (t:T.timestamp)
          (thread_id:thread_id)
          (vs:thread_state_t)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h -> U16.v s < length (v_thread vs h).model_store)
    (ensures fun h0 _ h1 ->
      U16.v s < length (v_thread vs h0).model_store /\
      v_thread vs h1 == vaddb_model (v_thread vs h0) s r t thread_id)
  = let h = get() in
    assert (U16.v s < length (v_thread vs h).model_store);

    let { T.record_key = k;
          T.record_value = v } = r in
    (* check value type consistent with key k *)
    if not (is_value_of k v)
    then (
      fail vs "vaddm: value is incompatible with key"
    )
    else (
      let ro = VCache.vcache_get_record vs.st s in
      if Some? ro
      then (
        fail vs "vaddm: slot s already exists"
      )
      else (
        prf_update_hash vs.hadd r t thread_id;// vs;
        update_clock t vs;
        VCache.vcache_add_record vs.st s k v T.BAdd)
    )

let vevictb (s:U16.t)
            (t:T.timestamp)
            (vs:thread_state_t)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h -> U16.v s < length (v_thread vs h).model_store)
    (ensures  fun h0 _ h1 ->
      U16.v s < length (v_thread vs h0).model_store /\
      v_thread vs h1 == vevictb_model (v_thread vs h0) s t vs.id)
  = let h = get() in
    assert (U16.v s < length (v_thread vs h).model_store);

    let clk = read vs.clock in
    if not (clk `timestamp_lt` t)
    then (
      fail vs "Timestamp is old"
    )
    else (
      (* check that the vstore contains s *)
      let r = VCache.vcache_get_record vs.st s in
      match r with
      | None ->
        fail vs "Slot is empty"

      | Some r ->
        (* update the evict hash *)
        prf_update_hash vs.hevict r t vs.id;

        update_clock t vs;

        VCache.vcache_evict_record vs.st s)
