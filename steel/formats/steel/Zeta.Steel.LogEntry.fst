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

let payload_of
  (relate_payload: bool)
  (x: Zeta.Steel.LogEntry.Types.log_entry0 relate_payload)
: GTot (option FStar.Bytes.bytes)
= match x with
  | AddM _ _ pl _
  | AddB _ _ _ pl _ ->
    begin match Ghost.reveal pl with
    | Inr pl -> Some (FStar.Bytes.hide (Ghost.reveal pl.ebytes))
    | _ -> None
    end
  | RunApp pl -> Some (FStar.Bytes.hide (Ghost.reveal pl.rest.ebytes))
  | _ -> None

let parse32_log_entry_filter_payload
  (relate_payload: bool)
  (p: Ghost.erased Zeta.Steel.LogEntry.Types.payload)
  (q: option FStar.Bytes.bytes)
: Pure bool
  (requires (
    match Ghost.reveal p, q with
    | Inl _, None -> True
    | Inr u, Some b -> FStar.Bytes.reveal b == Ghost.reveal u.Zeta.Steel.LogEntry.Types.ebytes
    | _ -> False
  ))
  (ensures (fun r ->
    r == parse_log_entry_filter_payload relate_payload p
  ))
= match q with
  | None -> true
  | Some u ->
    if relate_payload
    then 
      match parse32_app_record u with
      | None -> false
      | Some (_, n) -> n = FStar.Bytes.len u
    else true

let parse32_log_entry_filter
  (relate_payload: bool)
  (p: Zeta.Steel.LogEntry.Types.log_entry0 false)
  (q: option FStar.Bytes.bytes)
: Pure bool
  (requires (
    q == payload_of _ p
  ))
  (ensures (fun r ->
    r == parse_log_entry_filter relate_payload p
  ))
= match p with
  | Zeta.Steel.LogEntry.Types.AddM _ _ p _ -> parse32_log_entry_filter_payload relate_payload p q
  | Zeta.Steel.LogEntry.Types.AddB _ _ _ p _ -> parse32_log_entry_filter_payload relate_payload p q
  | _ -> true

let synth32_log_entry
  (relate_payload: bool)
  (p: LowParse.Spec.Combinators.parse_filter_refine (parse_log_entry_filter relate_payload))
  (q: option FStar.Bytes.bytes)
: Pure (Zeta.Steel.LogEntry.Types.log_entry0 relate_payload)
  (requires (
    q == payload_of _ p
  ))
  (ensures (fun r ->
    r == synth_log_entry relate_payload p
  ))
= match p with
  | Zeta.Steel.LogEntry.Types.AddM s s' p r0 ->
    let r = match q with
    | None -> r0
    | Some u ->
      if relate_payload
      then
        let Some ((k, v), _) = parse32_app_record u in
        (Zeta.Steel.LogEntry.Types.ApplicationKey k, Zeta.Steel.LogEntry.Types.DValue v)
      else r0
    in
    Zeta.Steel.LogEntry.Types.AddM s s' p r
  | Zeta.Steel.LogEntry.Types.AddB s ts tid p r0 ->
    let r = match q with
    | None -> r0
    | Some u ->
      if relate_payload
      then
        let Some ((k, v), _) = parse32_app_record u in
        (Zeta.Steel.LogEntry.Types.ApplicationKey k, Zeta.Steel.LogEntry.Types.DValue v)
      else r0
    in
    Zeta.Steel.LogEntry.Types.AddB s ts tid p r
  | Zeta.Steel.LogEntry.Types.RunApp pl ->
    Zeta.Steel.LogEntry.Types.RunApp pl
  | Zeta.Steel.LogEntry.Types.EvictM pl ->
    Zeta.Steel.LogEntry.Types.EvictM pl
  | Zeta.Steel.LogEntry.Types.EvictB pl ->
    Zeta.Steel.LogEntry.Types.EvictB pl
  | Zeta.Steel.LogEntry.Types.EvictBM pl ->
    Zeta.Steel.LogEntry.Types.EvictBM pl
  | Zeta.Steel.LogEntry.Types.NextEpoch ->
    Zeta.Steel.LogEntry.Types.NextEpoch
  | Zeta.Steel.LogEntry.Types.VerifyEpoch ->
    Zeta.Steel.LogEntry.Types.VerifyEpoch

module U32 = FStar.UInt32

#push-options "--z3rlimit 32 --ifuel 8"

let parse32_log_entry
  (relate_payload: bool)
: Tot (LowParse.SLow.Base.parser32 (Zeta.Formats.LogEntry.parse_log_entry relate_payload))
= fun b ->
  LowParse.Spec.Combinators.parse_synth_eq
    (LowParse.Spec.IfThenElse.parse_ifthenelse parse_ifthenelse_param
    `LowParse.Spec.Combinators.parse_filter` parse_log_entry_filter relate_payload)
    (synth_log_entry relate_payload)
    (FStar.Bytes.reveal b);
  LowParse.Spec.Combinators.parse_filter_eq
    (LowParse.Spec.IfThenElse.parse_ifthenelse parse_ifthenelse_param)
    (parse_log_entry_filter relate_payload)
    (FStar.Bytes.reveal b);
  LowParse.Spec.IfThenElse.parse_ifthenelse_eq parse_ifthenelse_param (FStar.Bytes.reveal b);
  match LowParse.SLow.IfThenElse.parse32_ifthenelse
    parse_ifthenelse_param
    Zeta.Formats.Aux.Log_entry_hdr.log_entry_hdr_parser32
    (fun t -> needs_payload t)
    (fun t -> if t then LowParse.SLow.Bytes.parse32_bounded_vlbytes 0 0ul 2147483647 2147483647ul else LowParse.SLow.Combinators.parse32_empty)
    (fun b t pl -> synth_log_entry_false t pl)
    b
  with
  | None -> None
  | Some (t, consumed_t) ->
    let Some (t0, consumed_hdr) = Zeta.Formats.Aux.Log_entry_hdr.log_entry_hdr_parser32 b in
    let b' = FStar.Bytes.slice b consumed_hdr (FStar.Bytes.len b) in 
    let q =
      if needs_payload t0 then
        let Some (pl, _) = LowParse.SLow.Bytes.parse32_bounded_vlbytes 0 0ul 2147483647 2147483647ul b' in
        Some (pl <: FStar.Bytes.bytes)
      else None
    in
    if parse32_log_entry_filter relate_payload t q
    then Some (synth32_log_entry relate_payload t q, consumed_t)
    else None

#pop-options

let parser_log_entry =
  Zeta.Steel.FormatsLib.mk_steel_parser (parse32_log_entry true)
