module Veritas.Steel.VerifierModel

open FStar.Ghost
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module MSH = Veritas.MultiSetHashDomain
module T = Veritas.Formats.Types

let data_key = T.key
let data_value = T.data_value
let thread_id = U16.t

let contents = Seq.seq (option T.record)
let model_hash = erased MSH.mset_ms_hashfn_dom

[@@erasable]
noeq
type thread_state_model = {
  model_failed : bool;
  model_store : contents;
  model_clock : erased U64.t;
  model_hadd : model_hash;
  model_hevict : model_hash;
}

let model_fail tsm = {tsm with model_failed=false}

let slot (tsm:thread_state_model) = i:U32.t{U32.v i < Seq.length tsm.model_store}

let model_get_record (tsm:thread_state_model) (s:slot tsm) : GTot (option T.record)
  = Seq.index tsm.model_store (U32.v s)

let model_put_record (tsm:thread_state_model) (s:slot tsm) (r:T.record)
  : thread_state_model
  = {tsm with model_store=Seq.upd tsm.model_store (U32.v s) (Some r)}

let model_evict_record (tsm:thread_state_model) (s:slot tsm)
  : thread_state_model
  = {tsm with model_store=Seq.upd tsm.model_store (U32.v s) None }

let vget_model (tsm:thread_state_model) (s:slot tsm) (v:T.value) : thread_state_model =
  match model_get_record tsm s with
  | None -> model_fail tsm
  | Some r ->
      if r.T.record_value <> v then model_fail tsm
      else tsm

let vput_model (tsm:thread_state_model) (s:slot tsm) (v:T.value) : thread_state_model
  = match model_get_record tsm s with
    | None -> model_fail tsm
    | Some r -> model_put_record tsm s ({r with T.record_value = v})

assume
val epoch_of_timestamp (t:T.timestamp) : U32.t
assume
val is_value_of (k:T.key) (v:T.value) : bool
assume
val is_data_key (k:T.key) : bool

let mk_record (k:T.key) (v:T.value{is_value_of k v}) (a:T.add_method) : T.record
  = {
      T.record_key = k;
      T.record_value = v;
      T.record_add_method = a;
      T.record_l_child_in_store = T.Vfalse;
      T.record_r_child_in_store = T.Vfalse
    }

let model_update_clock (tsm:thread_state_model) (ts:T.timestamp)
  : thread_state_model
  = if FStar.UInt.fits (U64.v tsm.model_clock + U64.v ts) 64
    then { tsm with model_clock = tsm.model_clock `U64.add` ts } //+1
    else model_fail tsm

assume
val model_update_hash (h:model_hash) (r:T.record) (t:T.timestamp) (thread_id:thread_id)
  : model_hash

let model_update_hadd (tsm:_) (r:T.record) (t:T.timestamp) (thread_id:thread_id) =
  ({tsm with model_hadd = model_update_hash tsm.model_hadd r t thread_id})

let model_update_hevict (tsm:_) (r:T.record) (t:T.timestamp) (thread_id:thread_id) =
  ({tsm with model_hevict = model_update_hash tsm.model_hevict r t thread_id})

let vaddb_model (tsm:thread_state_model) (s:slot tsm) (r:T.record) (t:T.timestamp) (thread_id:thread_id)
  : thread_state_model
  = let e = epoch_of_timestamp t in
    let { T.record_key = k;
          T.record_value = v } = r in
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
      model_put_record tsm s (mk_record k v T.BAdd)
    )

let timestamp_lt (t0 t1:T.timestamp) = t0 `U64.lt` t1

let vevictb_model (tsm:thread_state_model) (s:slot tsm) (t:T.timestamp) (thread_id:thread_id)
  : GTot thread_state_model
  = let e = epoch_of_timestamp t in
    let clk = tsm.model_clock in
    if not (clk `timestamp_lt` t)
    then model_fail tsm
    else begin
      (* check that the vstore contains s *)
      match model_get_record tsm s with
      | None -> model_fail tsm
      | Some r ->
        (* update the evict hash *)
        let tsm = model_update_hevict tsm r t thread_id in
        (* advance clock to t *)
        let tsm = model_update_clock tsm t in
        (* evict record *)
        model_evict_record tsm s
    end
