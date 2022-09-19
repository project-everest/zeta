module Zeta.KeyValueStore.Formats.Spec
include Zeta.KeyValueStore.Formats.Types

module A = Zeta.App
module P = Zeta.Steel.Parser

val key_spec_parser : P.spec_parser key_t

val key_spec_serializer : P.spec_serializer key_spec_parser

val value_spec_parser : P.spec_parser value_t

val value_spec_serializer : P.spec_serializer value_spec_parser

val vget_args_spec_parser : P.spec_parser vget_args_t

val vget_result_spec_parser : P.spec_parser vget_result_t

val vget_result_spec_serializer : P.spec_serializer vget_result_spec_parser

val vput_args_spec_parser : P.spec_parser vput_args_t

val vput_result_spec_parser : P.spec_parser vput_result_t

val vput_result_spec_serializer : P.spec_serializer vput_result_spec_parser

val nullable_value_parser : P.spec_parser value_nullable
