module Veritas.Steel.VCache
open Steel.Effect
open Steel.Effect.Atomic
open Steel.Memory
open Steel.FractionalPermission
open FStar.Ghost
module U32 = FStar.UInt32
open Steel.Array

val key : Type0
val value: Type0
val add_method : Type0
val is_value_of (k:key) (v:value)
  : bool
val record : Type0
val mk_record (k:key) (v:value{is_value_of k v}) (a:add_method) : record
val most_significant_bit (k:key) : bool
let is_data_key (k:key) : bool = most_significant_bit k

val vstore : Type0
let contents = Steel.Array.contents (option record)
val is_vstore (st:vstore) (c:contents) : slprop u#1

val vcache_create (_:unit) (n:U32.t)
  : SteelT vstore
           emp
           (fun v -> is_vstore v (Seq.create (U32.v n) None))

let slot_id (c:contents) = i:U32.t{U32.v i < length c}

val vcache_get_record (#c:contents) (vst:vstore) (s:slot_id c)
  : Steel (option record)
          (is_vstore vst c)
          (fun _ -> is_vstore vst c)
          (fun _ -> True)
          (fun _ res _ -> res == Seq.index c (U32.v s))

val vcache_set (#c:contents) (st:vstore) (s:slot_id c) (r:option record)
  : SteelT unit
      (is_vstore st c)
      (fun _ -> is_vstore st (Seq.upd c (U32.v s) r))


let vcache_update_record (#c:contents) (st:vstore) (s:slot_id c) (r:record)
  : SteelT unit
      (is_vstore st c)
      (fun _ -> is_vstore st (Seq.upd c (U32.v s) (Some r)))
  = vcache_set st s (Some r)


let vcache_add_record
      (#c:contents)
      (vst:vstore)
      (s:slot_id c)
      (k:key)
      (v:value{is_value_of k v})
      (a:add_method)
  : SteelT unit
      (is_vstore vst c)
      (fun _ -> is_vstore vst (Seq.upd c (U32.v s) (Some (mk_record k v a))))
  = vcache_update_record vst s (mk_record k v a)


let vcache_evict_record
      (#c:contents)
      (vst:vstore)
      (s:slot_id c)
  : SteelT unit
      (is_vstore vst c)
      (fun _ -> is_vstore vst (Seq.upd c (U32.v s) None))
  = vcache_set vst s None
