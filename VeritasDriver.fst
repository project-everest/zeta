module VeritasDriver
open FStar.All
open FStar.Integers
module V = Veritas.SparseMerkleVerifier
module IO = FStar.IO
module B = FStar.Bytes
module Parser = VeritasFormats

// This is to be integrated with Tahina's code
let parse_entry (b:B.bytes) (offset:uint_32{offset < B.len b})
  : option (V.verifier_log_entry & r:uint_32{offset < r /\ r <= B.len b})
  = let b' = B.sub b offset (B.len b - offset) in
    match Parser.parse_entry b' with
    | None -> None
    | Some (vle, i) ->
      assume (i > 0ul); //should be provable with LowParse ... discussing with Tahina
      Some (vle, i + offset)

let parse_log (b:B.bytes)
  : Tot (either V.verifier_log uint_32)
  = let rec aux out (offset:uint_32{offset <= B.len b})
     : Tot (either V.verifier_log uint_32)
           (decreases (v (B.len b - offset)))
     = if B.len b = offset
       then Inl (FStar.Seq.seq_of_list (List.Tot.rev out))
       else match parse_entry b offset with
            | None -> Inr offset
            | Some (e, offset) -> aux (e::out) offset
    in
    aux [] 0ul

let get_next_log ()
  : ML (either V.verifier_log uint_32)
  = parse_log (B.bytes_of_string IO.(read_line stdin))

let rec go (s:V.verifier_state)
  : ML unit
  = let log = get_next_log () in
    match log with
    | Inr err_pos ->
      IO.(write_string
             stderr
             (FStar.Printf.sprintf "Log parsing failed at position %ul\n" err_pos))

    | Inl log ->
      let s' = V.verifier_incremental log s in
      match s' with
      | V.Failed ->
        IO.(write_string stderr "Log verification failed\n")
      | _ -> go s'

#push-options "--warn_error -272" //intentional top-level effect okay
let main = go V.initial_verifier_state
