module Zeta.Steel.LogEntry.Spec

let spec_parser_log_entry b = match Zeta.Formats.LogEntry.parse_log_entry b with
  | None -> None
  | Some (res, consumed) -> Some (res, consumed)

let spec_serializer_log_entry x =
  assert (LowParse.Spec.Base.parse Zeta.Formats.LogEntry.parse_log_entry (Zeta.Formats.LogEntry.serialize_log_entry x) == Some (x, Seq.length (Zeta.Formats.LogEntry.serialize_log_entry x))); // pattern requires `LowParse.Spec.Base.parse`
  Zeta.Formats.LogEntry.serialize_log_entry x

let spec_parser_log_entry_consumes_at_least_one_byte bytes =
  let _ = LowParse.Spec.Base.parse Zeta.Formats.LogEntry.parse_log_entry bytes in // SMT pattern
  LowParse.Spec.Base.parser_kind_prop_equiv Zeta.Formats.LogEntry.parse_log_entry_kind Zeta.Formats.LogEntry.parse_log_entry

let spec_parser_log_entry_strong_prefix' (l l1:bytes)
  : Lemma
    (requires
       Some? (spec_parser_log_entry l) /\
       (let Some (le, pos) = spec_parser_log_entry l in
         pos <= Seq.length l1 /\
         Seq.slice l 0 pos `Seq.equal` Seq.slice l1 0 pos))
    (ensures (
       Some? (spec_parser_log_entry l) /\
       (let Some (le, pos) = spec_parser_log_entry l in (
         pos <= Seq.length l1 /\
         Seq.slice l 0 pos `Seq.equal` Seq.slice l1 0 pos) /\
         (match spec_parser_log_entry l1 with
          | None -> False
          | Some (le', pos') -> le' == le /\ eq2 #nat pos' pos /\ pos > 0))))
= 
  LowParse.Spec.Base.parse_strong_prefix Zeta.Formats.LogEntry.parse_log_entry l l1;
  spec_parser_log_entry_consumes_at_least_one_byte l1

let spec_parser_log_entry_strong_prefix bytes =
  Classical.forall_intro (Classical.move_requires (spec_parser_log_entry_strong_prefix' bytes))

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

let synth_stamped_record
  (x: Zeta.Formats.Aux.Stamped_record.stamped_record)
: Tot Zeta.Steel.LogEntry.Types.stamped_record
= {
  Zeta.Steel.LogEntry.Types.record = Zeta.Formats.Synth.synth_record x.sr_record;
  Zeta.Steel.LogEntry.Types.timestamp = x.sr_timestamp;
  Zeta.Steel.LogEntry.Types.thread_id = x.sr_thread_id;
}

let synth_stamped_record_recip
  (x: Zeta.Steel.LogEntry.Types.stamped_record)
: Tot Zeta.Formats.Aux.Stamped_record.stamped_record
= {
  sr_record = Zeta.Formats.Synth.synth_record_recip x.Zeta.Steel.LogEntry.Types.record;
  sr_timestamp = x.Zeta.Steel.LogEntry.Types.timestamp;
  sr_thread_id = x.Zeta.Steel.LogEntry.Types.thread_id;
}

module LPC = LowParse.Spec.Combinators

let spec_parser_stamped_record' =
  LPC.parse_synth
    Zeta.Formats.Aux.Stamped_record.stamped_record_parser
    synth_stamped_record

let spec_parser_stamped_record x =
  match LPC.parse spec_parser_stamped_record' x with
  | None -> None
  | Some (res, consumed) -> Some (res, consumed)

let spec_serializer_stamped_record' : LPC.serializer spec_parser_stamped_record' =
  LPC.serialize_synth
    _
    synth_stamped_record
    Zeta.Formats.Aux.Stamped_record.stamped_record_serializer
    synth_stamped_record_recip
    ()

let spec_serializer_stamped_record x = LPC.serialize spec_serializer_stamped_record' x

let serialized_stamped_record_length s = ()

let spec_parser_value' =
  LPC.parse_synth
    Zeta.Formats.Aux.Value.value_parser
    Zeta.Formats.Synth.synth_value

let spec_parser_value x =
  match LPC.parse spec_parser_value' x with
  | None -> None
  | Some (res, consumed) -> Some (res, consumed)

let spec_serializer_value' : LPC.serializer spec_parser_value' =
  LPC.serialize_synth
    _
    Zeta.Formats.Synth.synth_value
    Zeta.Formats.Aux.Value.value_serializer
    Zeta.Formats.Synth.synth_value_recip
    ()

let spec_serializer_value x = LPC.serialize spec_serializer_value' x

let serialized_value_length s = ()
