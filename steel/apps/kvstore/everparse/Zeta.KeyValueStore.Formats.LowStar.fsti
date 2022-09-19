module Zeta.KeyValueStore.Formats.LowStar
open Zeta.KeyValueStore.Formats.Spec

module A = Zeta.App
module P = Zeta.LowStar.Parser

/// NOTE: this module is actually implemented in Low*

val kvstore_key_parser : P.parser key_spec_parser

val kvstore_key_serializer : P.serializer key_spec_serializer

val kvstore_value_parser : P.parser value_spec_parser

val kvstore_value_serializer : P.serializer value_spec_serializer

val kvstore_vget_args_parser : P.parser vget_args_spec_parser

val kvstore_vput_args_parser : P.parser vput_args_spec_parser
