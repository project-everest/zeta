module Zeta.Steel.LogEntry.Spec

let spec_parser_log_entry = Zeta.Formats.LogEntry.parse_log_entry

let spec_serializer_log_entry x =
  assert (LowParse.Spec.Base.parse Zeta.Formats.LogEntry.parse_log_entry (Zeta.Formats.LogEntry.serialize_log_entry x) == Some (x, Seq.length (Zeta.Formats.LogEntry.serialize_log_entry x))); // pattern requires `LowParse.Spec.Base.parse`
  Zeta.Formats.LogEntry.serialize_log_entry x

let spec_parser_log_entry_consumes_at_least_one_byte bytes =
  let _ = LowParse.Spec.Base.parse Zeta.Formats.LogEntry.parse_log_entry bytes in // SMT pattern
  LowParse.Spec.Base.parser_kind_prop_equiv Zeta.Formats.LogEntry.parse_log_entry_kind Zeta.Formats.LogEntry.parse_log_entry

friend Zeta.Formats.LogEntry

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
  let h = Zeta.Formats.LogEntry.synth_log_entry_recip_hdr e in
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
