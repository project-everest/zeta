module Veritas.SteelSel.Verifier

open Steel.Memory
open Steel.SelEffect
open Steel.SelArray
open FStar.Ghost
module U32 = FStar.UInt32
module U64 = FStar.UInt64
open Veritas.SteelSel.VCache
open Veritas.Steel.Types

module MSH = Veritas.MultiSetHashDomain
let model_hash = erased MSH.mset_ms_hashfn_dom

[@@erasable]
noeq
type thread_state_model = {
  model_failed : bool;
  model_store  : VCache.contents;
  model_clock  : erased U64.t;
  model_hadd   : model_hash;
  model_hevict : model_hash;
}

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

let thread_id = U32.t
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




let model_fail tsm = {tsm with model_failed = false}

let fail (vs:thread_state_t) (msg:string)
  : SteelSelF unit
             (thread_state_inv vs)
             (fun _ -> thread_state_inv vs)
             (requires fun _ -> True)
             (ensures fun h0 _ h1 -> v_thread vs h1 == model_fail (v_thread vs h0))
  = write vs.failed false; ()

let slot (tsm:thread_state_model) = (i:U32.t{U32.v i < length tsm.model_store})

let vget_model (tsm:thread_state_model) (s:slot tsm) (v:value) : thread_state_model =
  match Seq.index tsm.model_store (U32.v s) with
  | None -> model_fail tsm
  | Some r' ->
    if v = r'.record_value then tsm else model_fail tsm

#push-options "--fuel 0 --ifuel 0"

let vget (s:U32.t) (v:value) (vs: thread_state_t)
  : SteelSel unit
             (thread_state_inv vs)
             (fun _ -> thread_state_inv vs)
             (requires fun h -> U32.v s < length (v_thread vs h).model_store)
             (ensures fun h0 _ h1 ->
               U32.v s < length (v_thread vs h0).model_store /\
               v_thread vs h1 == vget_model (v_thread vs h0) s v
             )
  = // AF: Unclear why this get is needed, already observed in smaller examples (cf linked lists).
    // Without it, the precondition on the selector of thread_state_inv is not propagated.
    // To debug
    let h = get () in
    let ro = VCache.vcache_get_record vs.st s in
    match ro with
    | None ->
      fail vs "Slot not found"
    | Some r' ->
      if v = r'.record_value
      // AF: Usual problem of SteelSel vs SteelSelF difference between the two branches
      then (noop (); ())
      else fail vs "Failed: inconsistent key or value in Get"

let model_get_record (tsm:thread_state_model) (s:slot tsm)
  : GTot (option record)
  = Seq.index tsm.model_store (U32.v s)

let model_put_record (tsm:thread_state_model) (s:slot tsm) (r:record)
  : thread_state_model
  = {tsm with model_store=Seq.upd tsm.model_store (U32.v s) (Some r)}

let model_evict_record (tsm:thread_state_model) (s:slot tsm)
  : thread_state_model
  = {tsm with model_store=Seq.upd tsm.model_store (U32.v s) None }

let vput_model (tsm:thread_state_model) (s:slot tsm) (v:value)
  : thread_state_model
  = match model_get_record tsm s with
    | None -> model_fail tsm
    | Some r -> model_put_record tsm s ({r with record_value=v})

(* verifier write operation *)
let vput (s:U32.t) (v:value) (vs: thread_state_t)
  : SteelSel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h -> U32.v s < length (v_thread vs h).model_store)
    (ensures fun h0 _ h1 ->
      U32.v s < length (v_thread vs h0).model_store /\
      v_thread vs h1 == vput_model (v_thread vs h0) s v)
  = let h = get() in
    let ro = VCache.vcache_get_record vs.st s in
    match ro with
    | None ->
      fail vs "Slot not found"

    | Some r ->
      // AF: Again, the SteelSel vs SteelSelF issue requires the extra unit
      vcache_update_record vs.st s ({ r with record_value = v });
      ()

val epoch_of_timestamp (t:timestamp) : U32.t

val mk_mhdom (r:record) (t:timestamp) (thread_id:thread_id) : MSH.ms_hashfn_dom

val model_update_hash (h:model_hash) (r:record) (t:timestamp) (thread_id:thread_id)
  : model_hash

val prf_update_hash (p:prf_set_hash) (r:record) (t:timestamp) (thread_id:thread_id)
  : SteelSel unit
    (prf_set_hash_inv p)
    (fun _ -> prf_set_hash_inv p)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 -> v_hash p h1 == model_update_hash (v_hash p h0) r t thread_id)

let model_update_hadd (tsm:_) (r:record) (t:timestamp) (thread_id:thread_id) =
  ({tsm with model_hadd = model_update_hash tsm.model_hadd r t thread_id})

let update_hadd (r:record) (t:timestamp) (thread_id:thread_id) (vs:thread_state_t)
  : SteelSel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      v_thread vs h1 == model_update_hadd (v_thread vs h0) r t thread_id)
  = // AF: Same as previously
    let h0 = get () in
    prf_update_hash vs.hadd r t thread_id;
    ()

let model_update_hevict (tsm:_) (r:record) (t:timestamp) (thread_id:thread_id) =
  ({tsm with model_hevict = model_update_hash tsm.model_hevict r t thread_id})

let update_hevict (r:record) (t:timestamp) (thread_id:thread_id) (vs:thread_state_t)
  : SteelSel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      v_thread vs h1 == model_update_hevict (v_thread vs h0) r t thread_id)
  = // AF: Same problem as previously
    let h0 = get() in
    prf_update_hash vs.hevict r t thread_id;
    ()

open FStar.Integers

let model_update_clock (tsm:thread_state_model) (ts:timestamp)
  : thread_state_model
  = if FStar.UInt.fits (U64.v tsm.model_clock + U64.v ts) 64
    then { tsm with model_clock = tsm.model_clock + ts } //+1
    else model_fail tsm

// AF: Requires some integers reasoningm, but should be straightforward
val update_clock (ts:timestamp) (vs:thread_state_t)
  : SteelSel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 -> v_thread vs h1 == model_update_clock (v_thread vs h0) ts)

val is_proper_descendent (k0 k1:key) : bool

let mk_record k v am = { record_key = k; record_value = v; record_add_method = am;
                         record_l_child_in_store = Vfalse;
                         record_r_child_in_store = Vfalse }

let vaddb_model (tsm:thread_state_model) (s:slot tsm) (r:record) (t:timestamp) (thread_id:thread_id)
  : thread_state_model
  = let e = epoch_of_timestamp t in
    let { record_key = k;
          record_value = v } = r in
    (* check value type consistent with key k *)
    if not (is_value_of k v) then model_fail tsm
    else if Some? (model_get_record tsm s) then model_fail tsm
    else (
      //TODO: need to check that the key does not exist
      (* updated h_add *)
      let tsm = model_update_hadd tsm r t thread_id in
      (* updated clock *)
      let tsm = model_update_clock tsm t in
      (* add record to store *)
      model_put_record tsm s (mk_record k v BAdd)
    )

let vaddb (s:U32.t)
          (r:record)
          (t:timestamp)
          (thread_id:thread_id)
          (vs:thread_state_t)
  : SteelSel unit
    (thread_state_inv vs)
    (fun _ -> thread_state_inv vs)
    (requires fun h -> U32.v s < length (v_thread vs h).model_store)
    (ensures fun h0 _ h1 ->
      U32.v s < length (v_thread vs h0).model_store /\
      v_thread vs h1 == vaddb_model (v_thread vs h0) s r t thread_id)
  = let h = get() in
    assert (U32.v s < length (v_thread vs h).model_store);
    (* epoch of timestamp of last evict *)
    let e = epoch_of_timestamp t in
    let { record_key = k;
          record_value = v } = r in
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
        //this next line is tricky for a couple of reasons
        // 1. the implicit arg to vcache_update_record is unified with the type of `s` which is indexed
        //    by the original tsm, not the current one
        // 2. the refinement type mk_record require `is_value_of k v` does not seem to be provable
        //    here. despite the check above.
        VCache.vcache_update_record vs.st s (mk_record k v BAdd)      )
    )
