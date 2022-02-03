module Zeta.Steel.LogEntry.Spec
include Zeta.Steel.LogEntry.Types
open Zeta.Steel.Parser
module U32 = FStar.UInt32
val spec_parser_log_entry : spec_parser log_entry

let can_parse_log_entry (log_bytes:bytes)
                        (log_pos:U32.t)
  = U32.v log_pos <= Seq.length log_bytes &&
    Some? (spec_parser_log_entry (Zeta.Steel.Parser.bytes_from log_bytes log_pos))

let spec_parse_log_entry (log_bytes:bytes)
                         (log_pos:U32.t{
                            can_parse_log_entry log_bytes log_pos
                          })
  : GTot (log_entry & nat)
  = parse_result log_bytes log_pos spec_parser_log_entry

let maybe_parse_log_entry (log_bytes:bytes)
                          (log_pos:U32.t)
  : GTot (option (log_entry & nat))
  = if can_parse_log_entry log_bytes log_pos
    then Some (spec_parse_log_entry log_bytes log_pos)
    else None

val spec_parser_log_entry_consumes_at_least_one_byte
  (log_bytes: bytes)
: Lemma
  (requires (Some? (spec_parser_log_entry log_bytes)))
  (ensures (
    let Some (_, consumed) = spec_parser_log_entry log_bytes in
    consumed >= 1
  ))

val runapp_payload_offset
  (e: log_entry)
  (b: Ghost.erased bytes)
: Pure U32.t
  (requires (
    RunApp? e /\
    begin match spec_parser_log_entry b with
    | Some (e', _) -> e' == e
    | _ -> False
    end
  ))
  (ensures (fun res ->
    let Some (_, len) = spec_parser_log_entry b in
    let off = U32.v res in
    let RunApp pl = e in
    off <= len /\
    Ghost.reveal pl.rest.ebytes == Seq.slice b off len
  ))
