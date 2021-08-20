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

let prf_set_hash = ref model_hash

let prf_set_hash_sl (x:prf_set_hash)
  = Steel.Memory.emp

let prf_set_hash_sel (r:prf_set_hash) : selector (model_hash) (prf_set_hash_sl r) = admit()

let prf_update_hash p r t thread_id = sladmit()

let update_clock (ts:T.timestamp) (vs:thread_state_t) = sladmit()

#push-options "--query_stats --log_queries --fuel 0 --ifuel 1"
#restart-solver
let fail vs msg = write vs.failed true; ()

let vget (s:U16.t) (k:T.key) (v:T.data_value) (vs: thread_state_t)
  = let ro = VCache.vcache_get_record vs.st s in
    match ro with
    | None ->
      fail vs "Slot not found"
    | Some r' ->
      if k <> r'.record_key
      then fail vs "Failed: inconsistent key in Get"
      else if T.V_dval v <> r'.record_value
      then fail vs "Failed: inconsistent value in Get"
      // AF: Usual problem of Steel vs SteelF difference between the two branches
      else (noop (); ())

(* verifier write operation *)
let vput (s:U16.t) (k:T.key) (v:T.data_value) (vs: thread_state_t)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h -> U16.v s < length (v_thread vs h).model_store)
    (ensures fun h0 _ h1 ->
      U16.v s < length (v_thread vs h0).model_store /\
      v_thread vs h1 == vput_model (v_thread vs h0) s k v)
  = let ro = VCache.vcache_get_record vs.st s in
    match ro with
    | None ->
      fail vs "Slot not found"

    | Some r ->
      if r.record_key <> k then fail vs "slot-key mismatch"
      else if not (is_data_key k) then fail vs "not a data key"
      else (
        vcache_update_record vs.st s ({ r with record_value = T.V_dval v });
        ()
      )


let vaddb (s:U16.t)
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
  = let h = get() in
    assert (U16.v s < length (v_thread vs h).model_store);

    let { T.record_key = k;
          T.record_value = v } = r in
    (* check value type consistent with key k *)
    if not (is_value_of k v)
    then (
      fail vs "vaddb: value is incompatible with key"
    )
    else (
      let ro = VCache.vcache_get_record vs.st s in
      if Some? ro
      then (
        fail vs "vaddb: slot s already exists"
      )
      else (
        prf_update_hash vs.hadd r t thread_id;// vs;
        update_clock t vs;
        VCache.vcache_add_record vs.st s k v T.BAdd)
    )

assume
val points_to_some_slot (s:U16.t)
                        (d:bool)
                        (vs:_)
  : Steel bool
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h -> U16.v s < length (v_thread vs h).model_store)
    (ensures fun h0 b h1 ->
      U16.v s < length (v_thread vs h0).model_store /\
      b == VerifierModel.points_to_some_slot (v_thread vs h0) s d /\
      v_thread vs h0 == v_thread vs h1)

val sat_evictb_checks (s:U16.t)
                      (t:T.timestamp)
                      (vs:_)
  : Steel bool
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h -> U16.v s < length (v_thread vs h).model_store)
    (ensures fun h0 b h1 ->
      U16.v s < length (v_thread vs h0).model_store /\
      b == VerifierModel.sat_evictb_checks (v_thread vs h0) s t /\
      v_thread vs h0 == v_thread vs h1)
let sat_evictb_checks s t vs
  = let ro = VCache.vcache_get_record vs.st s in
    match ro with
    | None -> Steel.Effect.Atomic.return false
    | Some r ->
      let clk = read vs.clock in
      if is_root r.record_key
      then Steel.Effect.Atomic.return false
      else if not (clk `timestamp_lt` t)
      then Steel.Effect.Atomic.return false
      else (
        let b1 = points_to_some_slot s true vs in
        let b2 = points_to_some_slot s false vs in
        not b1 && not b2
      )

assume
val vevictb_update_hash_clock
       (s:U16.t)
       (t:T.timestamp)
       (vs:_)
   : Steel unit
     (thread_state_inv vs)
     (fun _ -> thread_state_inv vs)
     (requires fun h0 ->
       U16.v s < length (v_thread vs h0).model_store /\
       VerifierModel.sat_evictb_checks (v_thread vs h0) s t)
     (ensures fun h0 _ h1 ->
       U16.v s < length (v_thread vs h0).model_store /\
       VerifierModel.sat_evictb_checks (v_thread vs h0) s t /\
       v_thread vs h1 ==
       model_vevictb_update_hash_clock (v_thread vs h0) s t)

assume
val bevict_from_store (s:U16.t) (vs:_)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h0 ->
       U16.v s < length (v_thread vs h0).model_store)
    (ensures fun h0 _ h1 ->
       U16.v s < length (v_thread vs h0).model_store /\
       v_thread vs h1 ==
       model_bevict_from_store (v_thread vs h0) s)

let vevictb (s:U16.t)
            (t:T.timestamp)
            (vs:thread_state_t)
  : Steel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h -> U16.v s < length (v_thread vs h).model_store)
    (ensures  fun h0 _ h1 ->
      U16.v s < length (v_thread vs h0).model_store /\
      v_thread vs h1 == vevictb_model (v_thread vs h0) s t)
  = let chk = sat_evictb_checks s t vs in
    if not chk then fail vs "sat_evictb_checks failed"
    else (
      let Some r = VCache.vcache_get_record vs.st s in
      if r.record_add_method <> T.BAdd
      then fail vs "Record is not a BAdd"
      else (
        vevictb_update_hash_clock s t vs;
        bevict_from_store s vs
      )
    )
