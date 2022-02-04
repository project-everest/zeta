module Zeta.Formats.Aux.Application_value.Low

open Zeta.Formats.Aux.Application_value.Spec
open LowParse.Low.Base

// NOTE TO APP DEVELOPERS: please implement these functions if you are using the Low* implementation of log entry parsers (in ../lowstar/)

val application_value_validator: validator application_value_parser
val application_value_jumper: jumper application_value_parser
val application_value_reader: leaf_reader application_value_parser
