module Zeta.Steel.LogEntry
include Zeta.Steel.LogEntry.Spec
open Zeta.Steel.Parser
module U32 = FStar.UInt32

val parser_log_entry : parser spec_parser_log_entry

val runapp_payload_offset
  (e: log_entry)
: Pure U32.t
  (requires (RunApp? e))
  (ensures (fun res ->
    let s = spec_serializer_log_entry e in
    let off = U32.v res in
    let RunApp pl = e in
    off <= Seq.length s /\
    Ghost.reveal pl.rest.ebytes == Seq.slice s off (Seq.length s)
  ))
