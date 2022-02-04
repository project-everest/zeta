module Zeta.Formats.Aux.Application_value.Spec
open Zeta.Steel.ApplicationTypes
open Zeta.Formats.Lib
open LowParse.Spec.Base

let application_value_parser : parser (strong_parser_kind 0 2040 None) _ =
  parser_intro value_type spec_parser_value spec_serializer_value spec_parser_value_injective spec_parser_value_strong_prefix 0 2040 serialized_value_length;
  bare_parser_of_spec_parser spec_parser_value

let application_value_serializer : serializer application_value_parser =
  spec_serializer_value
