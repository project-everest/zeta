module VeritasDriver
open FStar.All
open FStar.Integers
module V = Veritas.SparseMerkleVerifier
module IO = FStar.IO
module B = FStar.Bytes
module Parser = VeritasFormats

// This is to be integrated with Tahina's code
let parse_entry (b:B.bytes)
  : option (V.verifier_log_entry & r:B.bytes(*{B.len r < B.len b}*))
  = match Parser.parse_entry b with
    | None -> None
    | Some (vle, i) ->
//      assume (i > 0ul);
      let remaining = B.sub b i (B.len b - i) in
      Some (vle, remaining)

let parse_log (b:B.bytes)
  : Dv (option V.verifier_log)
  = let rec aux out (b:B.bytes)
     : Dv (option V.verifier_log)
//           (decreases (v (B.len b)))
     = if B.len b = 0ul
       then Some (FStar.Seq.seq_of_list (List.Tot.rev out))
       else match parse_entry b with
            | None -> None
            | Some (e, b) -> aux (e::out) b
    in
    aux [] b

let get_next_log ()
  : ML (option V.verifier_log)
  = parse_log (B.bytes_of_string IO.(read_line stdin))

let rec go (s:V.verifier_state)
  : ML unit
  = let log = get_next_log () in
    match log with
    | None ->
      IO.(write_string stderr "Log parsing failed\n")

    | Some log ->
      let s' = V.verifier_incremental log s in
      match s' with
      | V.Failed ->
        IO.(write_string stderr "Log verification failed\n")
      | _ -> go s'

#push-options "--warn_error -272" //intentional top-level effect okay
let main = go V.initial_verifier_state
