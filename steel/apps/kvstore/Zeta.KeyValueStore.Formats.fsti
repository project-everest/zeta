module Zeta.KeyValueStore.Formats

module A = Zeta.App
module P = Zeta.Steel.Parser

/// This module and its implementation is generated by EverParse
///   from respective format descriptions

type u16 = FStar.UInt16.t

val key_t : eqtype
val value_t : eqtype

val key_spec_parser : P.spec_parser key_t
val key_parser : P.parser key_spec_parser

val key_spec_serializer : P.spec_serializer key_spec_parser
val key_serializer : P.serializer key_spec_serializer

val value_spec_parser : P.spec_parser value_t
val value_parser : P.parser value_spec_parser

val value_spec_serializer : P.spec_serializer value_spec_parser
val value_serializer : P.serializer value_spec_serializer

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
