module Veritas.Formats
module LP = LowParse.Low.Base

friend Veritas.Formats.Pure

let serialize_value v dst =
  let _ = Veritas.Formats.EverParse.Value.value_lserializer v dst 0ul in ()   

module U64 = FStar.UInt64

let extract_log_entry_from len buf pos =
  let h = HST.get () in
  let sl = LP.make_slice buf len in
  let pos' = Veritas.Formats.EverParse.Vlog_entry.vlog_entry_validator sl (FStar.Int.Cast.uint32_to_uint64 pos) in
  if LP.is_error pos'
  then Inr (pos (* FIXME: constrain position in pos' *), "extract_log_entry: no valid log entry")
  else begin
    LP.valid_facts Veritas.Formats.EverParse.Vlog_entry.vlog_entry_parser h sl pos;
    LP.parse_strong_prefix Veritas.Formats.EverParse.Vlog_entry.vlog_entry_parser (LP.bytes_of_slice_from h sl pos) (B.as_seq h (B.gsub buf pos (LP.uint64_to_uint32 pos' `U32.sub` pos)));
    Inl (Veritas.Formats.EverParse.Vlog_entry.vlog_entry_reader sl pos, LP.uint64_to_uint32 pos')
  end

let serialize_stamped_record dst r =
  Veritas.Formats.EverParse.Stamped_record.stamped_record_lserializer r dst 0ul
