module Zeta.Formats.Aux.Application_key

friend Zeta.Formats.Aux.External.App
open Zeta.Steel.ApplicationTypes
open Zeta.Formats.Lib

let application_key_parser =
  parser_intro application_key spec_parser_key spec_serializer_key spec_parser_key_injective spec_parser_key_strong_prefix 0 2040 serialized_key_length;
  spec_parser_key

let application_key_serializer =
  spec_serializer_key

let application_key_bytesize x = Seq.length (spec_serializer_key x)

let application_key_bytesize_eq x = ()

assume val application_key_parser32': LS.parser32 application_key_parser
let application_key_parser32 = application_key_parser32'

assume val application_key_serializer32': LS.serializer32 application_key_serializer
let application_key_serializer32 = application_key_serializer32'

assume val application_key_size32': LS.size32 application_key_serializer
let application_key_size32 = application_key_size32'

assume val application_key_validator': LL.validator application_key_parser
let application_key_validator = application_key_validator'

assume val application_key_jumper': LL.jumper application_key_parser
let application_key_jumper = application_key_jumper'

assume val application_key_reader': LL.leaf_reader application_key_parser
let application_key_reader = application_key_reader'

assume val application_key_lserializer': LL.serializer32 application_key_serializer
let application_key_lserializer = application_key_lserializer'
