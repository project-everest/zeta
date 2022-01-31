module Zeta.Steel.LogEntry
include Zeta.Steel.LogEntry.Spec
open Zeta.Steel.Parser
module U32 = FStar.UInt32

val parser_log_entry : parser spec_parser_log_entry

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
