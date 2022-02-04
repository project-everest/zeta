module Zeta.Formats.Aux.Application_value

friend Zeta.Formats.Aux.External.App
open Zeta.Steel.ApplicationTypes
open Zeta.Formats.Lib

module Spec = Zeta.Formats.Aux.Application_value.Spec
module Size = Zeta.Formats.Aux.Application_value.Size
module SLow = Zeta.Formats.Aux.Application_value.SLow
module Low = Zeta.Formats.Aux.Application_value.Low

let application_value_parser = Spec.application_value_parser

let application_value_serializer = Spec.application_value_serializer

let application_value_bytesize x = Seq.length (spec_serializer_value x)

let application_value_bytesize_eq x = ()

// we need to add eta-expansions because the callees cannot be marked
// inline_for_extraction, since they are extern

let application_value_parser32 x = SLow.application_value_parser32 x

// this function is unused
assume val __UNUSED__application_value_serializer32': LS.serializer32 application_value_serializer
let application_value_serializer32 = __UNUSED__application_value_serializer32'

let application_value_size32 x = Size.application_value_size32 x

let application_value_validator input pos = Low.application_value_validator input pos

let application_value_jumper input pos = Low.application_value_jumper input pos

let application_value_reader input pos = Low.application_value_reader input pos

// unused
assume val __UNUSED__application_value_lserializer': LL.serializer32 application_value_serializer
let application_value_lserializer = __UNUSED__application_value_lserializer'
