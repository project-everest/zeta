module Zeta.Formats.Aux.Application_key.Spec
open Zeta.Steel.ApplicationTypes
open Zeta.Formats.Lib
open LowParse.Spec.Base

let application_key_parser : parser (strong_parser_kind 0 2040 None) _ =
  parser_intro key_type spec_parser_key spec_serializer_key spec_parser_key_injective spec_parser_key_strong_prefix 0 2040 serialized_key_length;
  spec_parser_key

let application_key_serializer : serializer application_key_parser =
  spec_serializer_key
