module Veritas.Formats
include Veritas.Formats.Parsers

let bool_of_vbool (x: vbool) : Tot bool =
  match x with
  | Vfalse -> false
  | Vtrue -> true

let vbool_of_bool (x: bool) : Tot vbool =
  if x then Vtrue else Vfalse
