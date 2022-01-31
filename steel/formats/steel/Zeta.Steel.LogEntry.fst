module Zeta.Steel.LogEntry

friend Zeta.Formats.LogEntry
friend Zeta.Steel.LogEntry.Spec
friend Zeta.Steel.ApplicationRecord
open Zeta.Formats.LogEntry
open Zeta.Steel.LogEntry.Types

let parse32_app_record : LowParse.SLow.Base.parser32 Zeta.Steel.ApplicationRecord.spec_parser_app_record' =
  LowParse.SLow.Combinators.parse32_nondep_then
    Zeta.Formats.Aux.Application_key.application_key_parser32
    (LowParse.SLow.Option.parse32_option Zeta.Formats.Aux.Application_value.application_value_parser32)

module U8 = FStar.UInt8
module U32 = FStar.UInt32

#push-options "--z3rlimit 32 --ifuel 8"

let parse32_log_entry
: LowParse.SLow.Base.parser32 Zeta.Formats.LogEntry.parse_log_entry
=
  LowParse.SLow.IfThenElse.parse32_ifthenelse
    parse_ifthenelse_param
    Zeta.Formats.Aux.Log_entry_hdr.log_entry_hdr_parser32
    (fun t -> needs_payload t)
    (fun t -> if t then LowParse.SLow.Bytes.parse32_bounded_vlbytes 0 0ul 2147483647 2147483647ul else LowParse.SLow.Combinators.parse32_empty)
    (fun b t pl -> synth_log_entry t pl)

#pop-options

let parser_log_entry =
  Zeta.Steel.FormatsLib.mk_steel_parser parse32_log_entry

let runapp_payload_offset'
  (e: log_entry)
: Pure U32.t
  (requires (RunApp? e))
  (ensures (fun res ->
    let s = Zeta.Formats.LogEntry.serialize_log_entry e in
    let RunApp r = e in
    let off = U32.v res in
    off <= Seq.length s /\
    Ghost.reveal r.rest.ebytes `Seq.equal` Seq.slice s off (Seq.length s)
  ))
=
  let RunApp r = e in
  let b = Ghost.hide (FStar.Bytes.hide (Ghost.reveal r.rest.ebytes)) in
  let h = synth_log_entry_recip_hdr e in
  assert (spec_serializer_log_entry e == Zeta.Formats.Aux.Log_entry_hdr.log_entry_hdr_serializer h `Seq.append` LowParse.Spec.Bytes.serialize_bounded_vlbytes 0 2147483647 (Ghost.reveal b));
  assert (LowParse.Spec.VLData.log256' 2147483647 == 4);
  LowParse.Spec.Combinators.serialize_synth_eq
    _
    (LowParse.Spec.Bytes.synth_bounded_vlbytes 0 2147483647)
    (LowParse.Spec.Bytes.serialize_bounded_vlbytes_aux 0 2147483647 4)
    (LowParse.Spec.Bytes.synth_bounded_vlbytes_recip 0 2147483647)
    ()
    (Ghost.reveal b)
  ;
  assert (LowParse.Spec.Bytes.serialize_bounded_vlbytes 0 2147483647 (Ghost.reveal b) == LowParse.Spec.VLData.serialize_bounded_integer 4 r.rest.len `Seq.append` r.rest.ebytes);
  Zeta.Formats.Aux.Log_entry_hdr.log_entry_hdr_size32 h `U32.add` 4ul

#push-options "--z3rlimit 32"

let runapp_payload_offset
  e b
=
  LowParse.Spec.Base.parse_injective Zeta.Formats.LogEntry.parse_log_entry b (Zeta.Formats.LogEntry.serialize_log_entry e);
  runapp_payload_offset' e

#pop-options
