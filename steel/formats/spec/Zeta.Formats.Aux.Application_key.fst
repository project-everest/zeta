module Zeta.Formats.Aux.Application_key

friend Zeta.Formats.Aux.External.App
open Zeta.Steel.ApplicationTypes
open Zeta.Formats.Lib

module Spec = Zeta.Formats.Aux.Application_key.Spec
module Size = Zeta.Formats.Aux.Application_key.Size
module SLow = Zeta.Formats.Aux.Application_key.SLow
module Low = Zeta.Formats.Aux.Application_key.Low

let application_key_parser = Spec.application_key_parser

let application_key_serializer = Spec.application_key_serializer

let application_key_bytesize x = Seq.length (spec_serializer_key x)

let application_key_bytesize_eq x = ()

// we need to add eta-expansions because the callees cannot be marked
// inline_for_extraction, since they are extern

let application_key_parser32 x = SLow.application_key_parser32 x

// this function is unused
assume val __UNUSED__application_key_serializer32': LS.serializer32 application_key_serializer
let application_key_serializer32 = __UNUSED__application_key_serializer32'

let application_key_size32 x = Size.application_key_size32 x

let application_key_validator input pos = Low.application_key_validator input pos

let application_key_jumper input pos = Low.application_key_jumper input pos

let application_key_reader input pos = Low.application_key_reader input pos

let application_key_lserializer v output pos = Low.application_key_lserializer v output pos
