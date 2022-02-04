module Zeta.LowStar.LogEntry

friend Zeta.Formats.LogEntry
friend Zeta.Steel.LogEntry.Spec
open Zeta.Formats.LogEntry
open Zeta.Steel.LogEntry.Types

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module LL = LowParse.Low.Base
module B = LowStar.Buffer

#push-options "--z3rlimit 32"
#restart-solver

let parser_log_entry
  len offset slice_len a
=
  let h = HST.get () in
  let sl_base = B.sub a offset slice_len in
  let sl = LowParse.Low.Base.make_slice sl_base slice_len in
  LL.valid_facts Zeta.Formats.LogEntry.parse_log_entry h sl 0ul;
  let consumed = LowParse.Low.IfThenElse.validate_ifthenelse
    Zeta.Formats.LogEntry.parse_ifthenelse_param
    Zeta.Formats.Aux.Log_entry_hdr.log_entry_hdr_validator
    (fun input pos ->
      let pos_tag = Zeta.Formats.Aux.Log_entry_hdr.log_entry_hdr_accessor_tag input pos in
      let tag = Zeta.Formats.Aux.Log_entry_kind.log_entry_kind_reader input pos_tag in
      tag = Zeta.Formats.Aux.Log_entry_kind.RunApp
    )
    (fun needs_payload ->
      if needs_payload
      then LowParse.Low.Bytes.validate_bounded_vlbytes 0 2147483647
      else LowParse.Low.Combinators.validate_empty ()
    )
    sl
    0uL
  in
  if LL.is_error consumed
  then None
  else begin
    let consumed = LL.uint64_to_uint32 consumed in
    LowParse.Low.IfThenElse.valid_ifthenelse_elim
      Zeta.Formats.LogEntry.parse_ifthenelse_param
      h
      sl
      0ul;
    let hdr = Zeta.Formats.Aux.Log_entry_hdr.log_entry_hdr_reader sl 0ul in
    if Zeta.Formats.Aux.Log_entry_hdr.Le_payload_RunApp? hdr
    then begin
      (* read the length of the payload, but not the payload itself *)
      let pos_pl = Zeta.Formats.Aux.Log_entry_hdr.log_entry_hdr_jumper sl 0ul in
      let len_pl = LowParse.Low.Bytes.bounded_vlbytes_payload_length 0 2147483647 sl pos_pl in
      let res = Zeta.Formats.LogEntry.synth_log_entry_true hdr (Ghost.hide (LL.contents (LowParse.Spec.Bytes.parse_bounded_vlbytes 0 2147483647) h sl pos_pl)) len_pl in
      Some (res, consumed)
    end else begin
      let res = Zeta.Formats.LogEntry.synth_log_entry_false hdr in
      Some (res, consumed)
    end
  end
