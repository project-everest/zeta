module Zeta.KeyValueStore.Formats

module A = Zeta.App
module P = Zeta.Steel.Parser
module KVS = Zeta.KeyValueStore.Spec

type u16 = FStar.UInt16.t

val key_spec_parser : P.spec_parser KVS.key_t
val key_parser : P.parser key_spec_parser

val key_spec_serializer : P.spec_serializer key_spec_parser
val key_serializer : P.serializer key_spec_serializer

val value_spec_parser : P.spec_parser KVS.value_t
val value_parser : P.parser value_spec_parser

val value_spec_serializer : P.spec_serializer value_spec_parser
val value_serializer : P.serializer value_spec_serializer

// What is the right place to include it from?
type slot_id = u16

type vget_args_t = {
  vget_key : KVS.key_t;
  vget_value : KVS.value_t;
  vget_slot : slot_id
}

type vget_result_t = unit

type vput_args_t = {
  vput_key : KVS.key_t;
  vput_value : KVS.value_t;
  vput_slot : slot_id
}

type vput_result_t = unit

val vget_args_spec_parser : P.spec_parser vget_args_t
val vget_args_parser : P.parser vget_args_spec_parser

val vget_result_spec_parser : P.spec_parser vget_result_t
val vget_result_parser : P.parser vget_result_spec_parser

val vget_args_spec_serializer : P.spec_serializer vget_args_spec_parser
val vget_args_serializer : P.serializer vget_args_spec_serializer

val vget_result_spec_serializer : P.spec_serializer vget_result_spec_parser
val vget_result_serializer : P.serializer vget_result_spec_serializer

val vput_args_spec_parser : P.spec_parser vput_args_t
val vput_args_parser : P.parser vput_args_spec_parser

val vput_result_spec_parser : P.spec_parser vput_result_t
val vput_result_parser : P.parser vput_result_spec_parser

val vput_args_spec_serializer : P.spec_serializer vput_args_spec_parser
val vput_args_serializer : P.serializer vput_args_spec_serializer

val vput_result_spec_serializer : P.spec_serializer vput_result_spec_parser
val vput_result_serializer : P.serializer vput_result_spec_serializer

val nullable_value_spec_parser : P.spec_parser (A.app_value_nullable KVS.adm)
