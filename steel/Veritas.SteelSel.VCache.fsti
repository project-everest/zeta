module Veritas.SteelSel.VCache
open Steel.Memory
open Steel.SelEffect
open FStar.Ghost
module U32 = FStar.UInt32
open Steel.SelArray
open Veritas.Steel.Types

// val key : Type0
// val value: Type0
// val add_method : Type0
val is_value_of (k:key) (v:value)
  : bool
val is_data_key (k:key) : bool
let mk_record (k:key) (v:value{is_value_of k v}) (a:add_method) : record
  = {
      record_key = k;
      record_value = v;
      record_add_method = a;
      record_l_child_in_store = Vfalse;
      record_r_child_in_store = Vfalse
    }

let vstore : Type0 = Steel.SelArray.array (option record)
let contents = Steel.SelArray.contents (option record)
let is_vstore (st:vstore) = varray st

val vcache_create (n:U32.t)
  : SteelSel vstore
             vemp
             (fun v -> is_vstore v)
             (requires fun _ -> True)
             (ensures fun _ v h1 -> asel v h1 == Seq.create (U32.v n) None)

let slot_id = U32.t

val vcache_get_record (vst:vstore) (s:slot_id)
  : SteelSel (option record)
             (is_vstore vst)
             (fun _ -> is_vstore vst)
             (requires fun h -> U32.v s < length (asel vst h))
             (ensures fun h0 res h1 ->
               U32.v s < length (asel vst h0) /\
               asel vst h0 == asel vst h1 /\
               res == Seq.index (asel vst h1) (U32.v s))

val vcache_set (st:vstore) (s:slot_id) (r:option record)
  : SteelSel unit
      (is_vstore st)
      (fun _ -> is_vstore st)
      (requires fun h -> U32.v s < length (asel st h))
      (ensures fun h0 _ h1 ->
        U32.v s < length (asel st h0) /\
        asel st h1 == Seq.upd (asel st h0) (U32.v s) r)

let vcache_update_record (st:vstore) (s:slot_id) (r:record)
  : SteelSel unit
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
      (k:key)
      (v:value{is_value_of k v})
      (a:add_method)
  : SteelSel unit
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
  : SteelSel unit
      (is_vstore vst)
      (fun _ -> is_vstore vst)
      (requires fun h -> U32.v s < length (asel vst h))
      (ensures fun h0 _ h1 ->
        U32.v s < length (asel vst h0) /\
        asel vst h1 == Seq.upd (asel vst h0) (U32.v s) None)
  = vcache_set vst s None
