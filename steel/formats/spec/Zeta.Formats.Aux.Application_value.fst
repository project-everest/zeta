module Zeta.Formats.Aux.Application_value

friend Zeta.Formats.Aux.External
open Zeta.Steel.ApplicationTypes
open Zeta.Formats.Lib

let application_value_parser =
  parser_intro application_value spec_parser_value spec_serializer_value spec_parser_value_injective spec_parser_value_strong_prefix 0 2040 serialized_value_length;
  spec_parser_value

let application_value_serializer =
  spec_serializer_value

let application_value_bytesize x = Seq.length (spec_serializer_value x)

let application_value_bytesize_eq x = ()

assume val application_value_parser32': LS.parser32 application_value_parser
let application_value_parser32 = application_value_parser32'

assume val application_value_serializer32': LS.serializer32 application_value_serializer
let application_value_serializer32 = application_value_serializer32'

assume val application_value_size32': LS.size32 application_value_serializer
let application_value_size32 = application_value_size32'

assume val application_value_validator': LL.validator application_value_parser
let application_value_validator = application_value_validator'

assume val application_value_jumper': LL.jumper application_value_parser
let application_value_jumper = application_value_jumper'
