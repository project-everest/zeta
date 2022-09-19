module Zeta.KeyValueStore.Formats.Types

module A = Zeta.App

type u8 = FStar.UInt8.t
type u16 = FStar.UInt16.t
type u64 = FStar.UInt64.t

let key_t : eqtype = u64
let value_t : eqtype = u64

type slot_id = u16

type vget_args_t = {
  vget_key : key_t;
  vget_value : value_t;
  vget_slot : slot_id
}

type vget_result_t = unit

type vput_args_t = {
  vput_key : key_t;
  vput_value : value_t;
  vput_slot : slot_id
}

type vput_result_t = unit

type value_nullable =
  | KV_null: value_nullable
  | KV_dvalue : value_t -> value_nullable
