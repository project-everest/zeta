module Zeta.Steel.ApplicationRecord

friend Zeta.Formats.Aux.Application_key
friend Zeta.Formats.Aux.Application_value

let spec_parser_app_record =
  LowParse.Spec.Combinators.nondep_then
    Zeta.Formats.Aux.Application_key.application_key_parser
    (LowParse.Spec.Option.parse_option Zeta.Formats.Aux.Application_value.application_value_parser)
