module Zeta.Steel.FormatsManual.Spec

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

let spec_parser_stamped_record x = LPC.parse spec_parser_stamped_record' x

let spec_serializer_stamped_record' : LPC.serializer spec_parser_stamped_record' =
  LPC.serialize_synth
    _
    synth_stamped_record
    Zeta.Formats.Aux.Stamped_record.stamped_record_serializer
    synth_stamped_record_recip
    ()

let spec_serializer_stamped_record x = LPC.serialize spec_serializer_stamped_record' x

let serialized_stamped_record_length s = ()
