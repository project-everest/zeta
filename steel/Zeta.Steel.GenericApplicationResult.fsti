module Zeta.Steel.GenericApplicationResult
include Zeta.Steel.ApplicationTypes

// A generic specification for parser specification for the result of app functions

module A = Zeta.App
module P = Zeta.Steel.Parser

val spec_result_parser (fid:A.appfn_id aprm)
  : P.spec_parser (app_result fid)

val spec_result_serializer (fid:A.appfn_id aprm)
  : P.spec_serializer (spec_result_parser fid)

val spec_app_result_entry_parser
  : P.spec_parser app_result_entry

val spec_app_result_entry_serializer
  : P.spec_serializer spec_app_result_entry_parser
