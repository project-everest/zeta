module Zeta.Formats.Aux.Application_key.Low

open Zeta.Formats.Aux.Application_key.Spec
open LowParse.Low.Base

// NOTE TO APP DEVELOPERS: please implement these functions if you are using the Low* implementation of log entry parsers (in ../lowstar/)

val application_key_validator: validator application_key_parser
val application_key_jumper: jumper application_key_parser
val application_key_reader: leaf_reader application_key_parser
val application_key_lserializer: serializer32 application_key_serializer
