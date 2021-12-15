module Zeta.Steel.Parser

let spec_parse_pair p0 p1 b =
  match p0 b with
  | None -> None
  | Some (x0, n0) ->
    begin match p1 (Seq.slice b n0 (Seq.length b)) with
    | None -> None
    | Some (x1, n1) -> Some ((x0, x1), n0 + n1)
    end
