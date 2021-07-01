module Veritas.Steel.VerifierModel

open FStar.Ghost
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module MSH = Veritas.MultiSetHashDomain
module T = Veritas.Formats.Types

let data_key = T.key
let data_value = T.data_value

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
