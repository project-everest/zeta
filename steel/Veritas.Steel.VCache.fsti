module Veritas.Steel.VCache

open Steel.Memory
open Steel.Effect
open Steel.Effect.Atomic
open Steel.FractionalPermission
open FStar.Ghost
module U32 = FStar.UInt32
open Steel.Array

module T = Veritas.Formats.Types
open Veritas.Steel.VerifierModel

let vstore : Type0 = Steel.Array.array (option T.record)
unfold
let is_vstore (st:vstore) = varray st

val vcache_create (n:U32.t)
  : Steel vstore
           emp
           (fun v -> is_vstore v)
           (requires fun _ -> True)
           (ensures fun _ v h1 -> asel v h1 == Seq.create (U32.v n) None)

let slot_id = U32.t

val vcache_get_record (vst:vstore) (s:slot_id)
  : Steel (option T.record)
          (is_vstore vst)
          (fun _ -> is_vstore vst)
          (requires fun h -> U32.v s < length (asel vst h))
          (ensures fun h0 res h1 ->
             U32.v s < length (asel vst h0) /\
             asel vst h0 == asel vst h1 /\
             res == Seq.index (asel vst h1) (U32.v s))

val vcache_set (st:vstore) (s:slot_id) (r:option T.record)
  : Steel unit
      (is_vstore st)
      (fun _ -> is_vstore st)
      (requires fun h -> U32.v s < length (asel st h))
      (ensures fun h0 _ h1 ->
        U32.v s < length (asel st h0) /\
        asel st h1 == Seq.upd (asel st h0) (U32.v s) r)

let vcache_update_record (st:vstore) (s:slot_id) (r:T.record)
  : Steel unit
      (is_vstore st)
      (fun _ -> is_vstore st)
      (requires fun h -> U32.v s < length (asel st h))
      (ensures fun h0 _ h1 ->
        U32.v s < length (asel st h0) /\
        asel st h1 == Seq.upd (asel st h0) (U32.v s) (Some r))
  = vcache_set st s (Some r)

let vcache_add_record
      (vst:vstore)
      (s:slot_id)
      (k:T.key)
      (v:T.value{is_value_of k v})
      (a:T.add_method)
  : Steel unit
      (is_vstore vst)
      (fun _ -> is_vstore vst)
      (requires fun h -> U32.v s < length (asel vst h))
      (ensures fun h0 _ h1 ->
        U32.v s < length (asel vst h0) /\
        asel vst h1 == Seq.upd (asel vst h0) (U32.v s) (Some (mk_record k v a)))
  = vcache_update_record vst s (mk_record k v a)

let vcache_evict_record
      (vst:vstore)
      (s:slot_id)
  : Steel unit
      (is_vstore vst)
      (fun _ -> is_vstore vst)
      (requires fun h -> U32.v s < length (asel vst h))
      (ensures fun h0 _ h1 ->
        U32.v s < length (asel vst h0) /\
        asel vst h1 == Seq.upd (asel vst h0) (U32.v s) None)
  = vcache_set vst s None
