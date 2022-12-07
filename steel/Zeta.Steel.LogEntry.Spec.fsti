module Zeta.Steel.LogEntry.Spec
include Zeta.Steel.LogEntry.Types
open Zeta.Steel.Parser
module U8 = FStar.UInt8
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

val spec_parser_log_entry_strong_prefix (l:bytes)
  : Lemma
    (requires
       Some? (spec_parser_log_entry l))
    (ensures (
       let Some (le, pos) = spec_parser_log_entry l in
       (forall (l1:bytes).{:pattern spec_parser_log_entry l1}
         pos <= Seq.length l1 /\
         Seq.slice l 0 pos `Seq.equal` Seq.slice l1 0 pos ==>
         (match spec_parser_log_entry l1 with
          | None -> False
          | Some (le', pos') -> le' == le /\ eq2 #nat pos' pos /\ pos > 0))))

val zeta__runapp_payload_offset
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

inline_for_extraction
noextract
let runapp_payload_offset = zeta__runapp_payload_offset

val spec_parser_stamped_record : spec_parser stamped_record
val spec_serializer_stamped_record : spec_serializer spec_parser_stamped_record

/// This is an ad hoc bound due to a bound on Blake hashable inputs
val serialized_stamped_record_length (s:stamped_record)
  : Lemma (Seq.length (spec_serializer_stamped_record s) <= 4096)

val spec_parser_value : spec_parser value
val spec_serializer_value : spec_serializer spec_parser_value
val serialized_value_length (s:value)
  : Lemma (Seq.length (spec_serializer_value s) <= 4096)
          [SMTPat (Seq.length (spec_serializer_value s))]

val spec_parser_u256 : spec_parser u256

val spec_parser_u256_never_fails (b:Seq.seq U8.t { Seq.length b == 32 })
  : Lemma (match spec_parser_u256 b with
           | None -> False
           | Some (_, n) -> n == 32)

val spec_parser_iv : spec_parser timestamp
val spec_serializer_iv: spec_serializer spec_parser_iv
val serialized_iv_length (s:timestamp)
  : Lemma (Seq.length (spec_serializer_iv s) == 96)
