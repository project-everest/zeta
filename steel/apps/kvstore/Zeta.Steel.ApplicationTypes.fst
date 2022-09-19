module Zeta.Steel.ApplicationTypes

module S = Zeta.KeyValueStore.Spec
module F = Zeta.KeyValueStore.Formats

/// Implementation of the steel/Zeta.Steel.ApplicationsTypes interface
///   for the key value store app

type key_type = F.key_t

let spec_parser_key = F.key_spec_parser
let parse_key = F.kvstore_key_parser
let spec_serializer_key = F.key_spec_serializer
let serialize_key = F.kvstore_key_serializer

/// The following admits depend on the exact types we choose for keys and values

//
// TODO DETAILS
//

let spec_parser_key_injective b1 b2 = admit ()

let spec_parser_key_strong_prefix b1 b2 = admit ()

let serialized_key_length v = admit ()

type value_type = F.value_t

let eq_value_type v0 v1 = admit ()

let spec_parser_value = F.value_spec_parser
let parse_value = F.kvstore_value_parser

let spec_serializer_value = F.value_spec_serializer
let serialize_value = F.kvstore_value_serializer

let spec_parser_value_injective b1 b2 = admit ()

let spec_parser_value_strong_prefix b1 b2 = admit ()

let serialized_value_length v = admit ()

let aprm = S.kv_params

//
// TODO DETAILS
//
let store_size = 16us
let n_threads = 16ul

let vget_args_synth_f (x:F.vget_args_t)
  : app_args S.vget_id & slots S.vget_id
  = (x.vget_key, x.vget_value), Seq.create 1 x.vget_slot


let vget_args_spec_parser
  : P.spec_parser (app_args S.vget_id &
                   slots S.vget_id)
  = fun b ->
    match F.vget_args_spec_parser b with
    | None -> None
    | Some (x, consumed) -> Some (vget_args_synth_f x, consumed)

let vput_args_synth_f (x:F.vput_args_t)
  : app_args S.vput_id & slots S.vput_id
  = (x.vput_key, x.vput_value), Seq.create 1 x.vput_slot

let vput_args_spec_parser
  : P.spec_parser (app_args S.vput_id &
                   slots S.vput_id)
  = fun b ->
    match F.vput_args_spec_parser b with
    | None -> None
    | Some (x, consumed) -> Some (vput_args_synth_f x, consumed)

let spec_app_parser fid =
  if fid = S.vget_id
  then vget_args_spec_parser
  else vput_args_spec_parser

(*
let spec_result_parser fid =
  if fid = S.vget_id
  then F.vget_result_spec_parser
  else F.vput_result_spec_parser

let spec_result_serializer fid =
  if fid = S.vget_id
  then F.vget_result_spec_serializer
  else F.vput_result_spec_serializer

//
// TODO: these are dependent records
//       can we generate these using EverParse
//         or we need to implement them?
//
let spec_app_result_entry_parser = admit ()
let spec_app_result_entry_serializer = admit ()
