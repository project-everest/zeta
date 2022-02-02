module Zeta.Steel.LogEntry.Spec
include Zeta.Steel.LogEntry.Types
open Zeta.Steel.Parser
module U32 = FStar.UInt32
val spec_parser_log_entry : spec_parser log_entry

let can_parse_log_entry (log_bytes:bytes)
                        (log_pos:U32.t{  U32.v log_pos < Seq.length log_bytes })
  : prop
  = Some? (spec_parser_log_entry (Zeta.Steel.Parser.bytes_from log_bytes log_pos)) == true

let spec_parse_log_entry (log_bytes:bytes)
                         (log_pos:U32.t{
                            U32.v log_pos < Seq.length log_bytes /\
                            can_parse_log_entry log_bytes log_pos
                          })
  : GTot (log_entry & nat)
  = parse_result log_bytes log_pos spec_parser_log_entry

val spec_parser_log_entry_consumes_at_least_one_byte
  (log_bytes: bytes)
: Lemma
  (requires (Some? (spec_parser_log_entry log_bytes)))
  (ensures (
    let Some (_, consumed) = spec_parser_log_entry log_bytes in
    consumed >= 1
  ))
