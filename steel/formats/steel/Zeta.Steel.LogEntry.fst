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
  Zeta.Steel.FormatsLib.mk_steel_parser parse32_log_entry spec_parser_log_entry ()

let serialize32_stamped_record : LowParse.SLow.Base.serializer32 spec_serializer_stamped_record' =
  LowParse.SLow.Combinators.serialize32_synth'
    _
    synth_stamped_record
    _
    Zeta.Formats.Aux.Stamped_record.stamped_record_serializer32
    synth_stamped_record_recip
    ()

let serialize_stamped_record =
  Zeta.Steel.FormatsLib.mk_steel_serializer serialize32_stamped_record spec_serializer_stamped_record ()

let serialize32_value : LowParse.SLow.Base.serializer32 spec_serializer_value' =
  LowParse.SLow.Combinators.serialize32_synth'
    _
    Zeta.Formats.Synth.synth_value
    _
    Zeta.Formats.Aux.Value.value_serializer32
    Zeta.Formats.Synth.synth_value_recip
    ()

let serialize_value =
  Zeta.Steel.FormatsLib.mk_steel_serializer serialize32_value spec_serializer_value ()

let parse32_u256
: LowParse.SLow.Base.parser32 Zeta.Steel.LogEntry.Spec.u256_parser'
= LowParse.SLow.Combinators.parse32_synth' _ Zeta.Formats.Synth.synth_u256  Zeta.Formats.Aux.U256.u256_parser32 ()

let parser_u256 =
  Zeta.Steel.FormatsLib.mk_steel_parser parse32_u256 spec_parser_u256 ()
