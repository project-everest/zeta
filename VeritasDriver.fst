module VeritasDriver
open FStar.All
module V = Veritas.SparseMerkleVerifier
module IO = FStar.IO
module B = FStar.Bytes


// This is to be integrated with Tahina's code
val parse_log (b:B.bytes) : option V.verifier_log

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
