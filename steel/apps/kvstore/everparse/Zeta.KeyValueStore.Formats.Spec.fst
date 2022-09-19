module Zeta.KeyValueStore.Formats.Spec

module LP = LowParse.Spec
module L = Zeta.Formats.Lib

let parse_key = LP.parse_u64

let key_spec_parser = L.spec_parser_of_bare_parser parse_key

let key_spec_serializer = fun x -> LP.serialize_u64 x

let parse_value = LP.parse_u64

let key_spec_parser_injective b1 b2 =
  LP.parse_injective parse_key b1 b2

let key_spec_parser_strong_prefix b1 b2 =
  LP.parse_strong_prefix parse_key b1 b2

let serialized_key_length x =
  LP.serialize_length LP.serialize_u64 x

let value_spec_parser = L.spec_parser_of_bare_parser parse_value

let value_spec_serializer = fun x ->  LP.serialize_u64 x

let value_spec_parser_injective b1 b2 =
  LP.parse_injective parse_value b1 b2

let value_spec_parser_strong_prefix b1 b2 =
  LP.parse_strong_prefix parse_value b1 b2

let serialized_value_length x =
  LP.serialize_length LP.serialize_u64 x

let synth_vget_args ((vget_key, vget_value), vget_slot) = {
  vget_key = vget_key;
  vget_value = vget_value;
  vget_slot = vget_slot;
}

let parse_vget_args =
  LP.parse_u64 `LP.nondep_then` LP.parse_u64
    `LP.nondep_then` LP.parse_u16
    `LP.parse_synth` synth_vget_args

let vget_args_spec_parser = L.spec_parser_of_bare_parser parse_vget_args

let parse_vget_result = LP.parse_empty

let vget_result_spec_parser = L.spec_parser_of_bare_parser parse_vget_result

let vget_result_spec_serializer = fun x -> LP.serialize_empty x

let synth_vput_args ((vput_key, vput_value), vput_slot) = {
  vput_key = vput_key;
  vput_value = vput_value;
  vput_slot = vput_slot;
}

let parse_vput_args =
  LP.parse_u64 `LP.nondep_then` LP.parse_u64
    `LP.nondep_then` LP.parse_u16
    `LP.parse_synth` synth_vput_args

let vput_args_spec_parser = L.spec_parser_of_bare_parser parse_vput_args

let parse_vput_result = LP.parse_empty

let vput_result_spec_parser = L.spec_parser_of_bare_parser parse_vput_result

let vput_result_spec_serializer = fun x -> LP.serialize_empty x

let enum_value_nullable : LP.enum FStar.UInt8.t FStar.UInt8.t =
  [0uy, 0uy; 1uy, 1uy]

inline_for_extraction
noextract
let sum_value_nullable = LP.Sum
  _
  _
  enum_value_nullable
  value_nullable
  (function KV_null -> 0uy | _ -> 1uy)
  (function 0uy -> unit | _ -> value_t)
  (function 0uy -> (fun _ -> KV_null) | _ -> (fun x -> KV_dvalue x))
  (function 0uy -> (fun _ -> ()) | _ -> KV_dvalue?._0)
  (fun _ _ -> ())
  (fun _ -> ())

let parse_sum_value_nullable = LP.parse_sum
  sum_value_nullable
  LP.parse_u8
  (function 0uy -> (| _, LP.parse_empty |) | _ -> (| _, parse_value |))

let nullable_value_parser = L.spec_parser_of_bare_parser parse_sum_value_nullable
