module Zeta.Formats.LogEntry

let needs_payload
  (x: Zeta.Formats.Aux.Log_entry_hdr.log_entry_hdr)
: Tot bool
= let open Zeta.Formats.Aux.Log_entry_hdr in
  match x with
  | Le_payload_AddMApp _
  | Le_payload_AddBApp _
  | Le_payload_RunApp _
    -> true
  | _ -> false

let payload (needs_payload: bool) : Tot Type0 =
  if needs_payload
  then LowParse.Spec.Bytes.parse_bounded_vlbytes_t 0 2147483647
  else unit

let payload_parser (needs_payload: bool) : Tot (k: LP.parser_kind & LP.parser k (payload needs_payload)) =
  if needs_payload
  then (| _, LowParse.Spec.Bytes.parse_bounded_vlbytes 0 2147483647 |)
  else (| _, LowParse.Spec.Combinators.parse_empty |)

open Zeta.Formats.Aux.Addm_payload
open Zeta.Formats.Aux.Addmapp_payload_hdr
open Zeta.Formats.Aux.Addb_payload
open Zeta.Formats.Aux.Addbapp_payload_hdr
open Zeta.Formats.Aux.Evictm_payload
open Zeta.Formats.Aux.Evictb_payload
open Zeta.Formats.Aux.Evictbm_payload
open Zeta.Formats.Synth

let synth_log_entry_false
  (x: Zeta.Formats.Aux.Log_entry_hdr.log_entry_hdr)
  (pl: payload (needs_payload x))
: Tot (Zeta.Steel.LogEntry.Types.log_entry0 false)
= match x with
  | Zeta.Formats.Aux.Log_entry_hdr.Le_payload_AddM apl ->
    let k = synth_key apl.addm_k in
    let v = synth_mval_value apl.addm_v in
    Zeta.Steel.LogEntry.Types.AddM
      apl.addm_s
      apl.addm_s2
      (Inl (k, v))
      (k, Zeta.Steel.LogEntry.Types.MValue v)
  | Zeta.Formats.Aux.Log_entry_hdr.Le_payload_AddMApp apl ->
    Zeta.Steel.LogEntry.Types.AddM
      apl.addmapp_s
      apl.addmapp_s2
      (Inr (Zeta.Steel.LogEntry.Types.Mkuninterpreted (FStar.Bytes.len pl) (FStar.Bytes.reveal pl)))
      Zeta.Steel.LogEntry.Types.dummy_record
  | Zeta.Formats.Aux.Log_entry_hdr.Le_payload_AddB apl ->
    let k = synth_key apl.addb_k in
    let v = synth_mval_value apl.addb_v in
    Zeta.Steel.LogEntry.Types.AddB
      apl.addb_s
      apl.addb_t
      apl.addb_tid
      (Inl (k, v))
      (k, Zeta.Steel.LogEntry.Types.MValue v)
  | Zeta.Formats.Aux.Log_entry_hdr.Le_payload_AddBApp apl ->
    Zeta.Steel.LogEntry.Types.AddB
      apl.addbapp_s
      apl.addbapp_t
      apl.addbapp_tid
      (Inr (Zeta.Steel.LogEntry.Types.Mkuninterpreted (FStar.Bytes.len pl) (FStar.Bytes.reveal pl)))
      Zeta.Steel.LogEntry.Types.dummy_record
  | Zeta.Formats.Aux.Log_entry_hdr.Le_payload_RunApp rpl ->
    Zeta.Steel.LogEntry.Types.RunApp
      (Zeta.Steel.LogEntry.Types.MkrunApp_payload
        rpl
        (Zeta.Steel.LogEntry.Types.Mkuninterpreted (FStar.Bytes.len pl) (FStar.Bytes.reveal pl))
      )
  | Zeta.Formats.Aux.Log_entry_hdr.Le_payload_NextEpoch _ ->
    Zeta.Steel.LogEntry.Types.NextEpoch
  | Zeta.Formats.Aux.Log_entry_hdr.Le_payload_VerifyEpoch _ ->
    Zeta.Steel.LogEntry.Types.VerifyEpoch
  | Zeta.Formats.Aux.Log_entry_hdr.Le_payload_EvictM epl ->
    Zeta.Steel.LogEntry.Types.EvictM
      (Zeta.Steel.LogEntry.Types.MkevictM_payload epl.evictm_s epl.evictm_s2)
  | Zeta.Formats.Aux.Log_entry_hdr.Le_payload_EvictB epl ->
    Zeta.Steel.LogEntry.Types.EvictB
      (Zeta.Steel.LogEntry.Types.MkevictB_payload epl.evictb_s epl.evictb_t)
  | Zeta.Formats.Aux.Log_entry_hdr.Le_payload_EvictBM epl ->
    Zeta.Steel.LogEntry.Types.EvictBM
      (Zeta.Steel.LogEntry.Types.MkevictBM_payload epl.evictbm_s epl.evictbm_s2 epl.evictbm_t)

let parse_ifthenelse_param =
  LowParse.Spec.IfThenElse.Mkparse_ifthenelse_param
    _ _
    Zeta.Formats.Aux.Log_entry_hdr.log_entry_hdr_parser
    needs_payload
    payload
    payload_parser
    _
    synth_log_entry_false
    (fun t1 x1 t2 x2 -> ())

let parse_log_entry_filter_payload
  (relate_payload: bool)
  (p: Zeta.Steel.LogEntry.Types.payload)
: GTot bool
= match p with
  | Inl _ -> true
  | Inr u ->
    if relate_payload
    then 
      match Zeta.Steel.ApplicationRecord.spec_parser_app_record u.Zeta.Steel.LogEntry.Types.ebytes with
      | None -> false
      | Some (_, n) -> n = FStar.UInt32.v u.Zeta.Steel.LogEntry.Types.len
    else true

let parse_log_entry_filter
  (relate_payload: bool)
  (p: Zeta.Steel.LogEntry.Types.log_entry0 false)
: GTot bool
= match p with
  | Zeta.Steel.LogEntry.Types.AddM _ _ p _ -> parse_log_entry_filter_payload relate_payload p
  | Zeta.Steel.LogEntry.Types.AddB _ _ _ p _ -> parse_log_entry_filter_payload relate_payload p
  | _ -> true

let synth_log_entry
  (relate_payload: bool)
  (p: LowParse.Spec.Combinators.parse_filter_refine (parse_log_entry_filter relate_payload))
: GTot (Zeta.Steel.LogEntry.Types.log_entry0 relate_payload)
= match p with
  | Zeta.Steel.LogEntry.Types.AddM s s' p r0 ->
    let r = match Ghost.reveal p with
    | Inl _ -> r0
    | Inr u ->
      if relate_payload
      then
        let Some ((k, v), _) = Zeta.Steel.ApplicationRecord.spec_parser_app_record u.Zeta.Steel.LogEntry.Types.ebytes in
        (Zeta.Steel.LogEntry.Types.ApplicationKey k, Zeta.Steel.LogEntry.Types.DValue v)
      else r0
    in
    Zeta.Steel.LogEntry.Types.AddM s s' p r
  | Zeta.Steel.LogEntry.Types.AddB s ts tid p r0 ->
    let r = match Ghost.reveal p with
    | Inl _ -> r0
    | Inr u ->
      if relate_payload
      then
        let Some ((k, v), _) = Zeta.Steel.ApplicationRecord.spec_parser_app_record u.Zeta.Steel.LogEntry.Types.ebytes in
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

let parse_log_entry_kind = LowParse.Spec.Combinators.parse_filter_kind (LowParse.Spec.IfThenElse.parse_ifthenelse_kind parse_ifthenelse_param)

let parse_log_entry relate_payload =
  LowParse.Spec.IfThenElse.parse_ifthenelse parse_ifthenelse_param
    `LowParse.Spec.Combinators.parse_filter` parse_log_entry_filter relate_payload
    `LowParse.Spec.Combinators.parse_synth` synth_log_entry relate_payload

let payload_serializer (needs_payload: bool) : Tot (LP.serializer (dsnd (payload_parser needs_payload))) =
  if needs_payload
  then LowParse.Spec.Bytes.serialize_bounded_vlbytes 0 2147483647
  else LowParse.Spec.Combinators.serialize_empty

let payload_serializer' (needs_payload: bool) : Tot (LP.serializer (dsnd (parse_ifthenelse_param.LowParse.Spec.IfThenElse.parse_ifthenelse_payload_parser needs_payload))) = payload_serializer needs_payload

let synth_log_entry_false_recip
  (y: Zeta.Steel.LogEntry.Types.log_entry0 false)
: GTot (t: Zeta.Formats.Aux.Log_entry_hdr.log_entry_hdr & payload (needs_payload t))
= match y with
  | Zeta.Steel.LogEntry.Types.AddM s s2 p _ ->
    begin match Ghost.reveal p with
    | Inl (k, v) ->
      (| Zeta.Formats.Aux.Log_entry_hdr.Le_payload_AddM ({
        addm_k = synth_key_recip k;
        addm_v = synth_mval_value_recip v;
        addm_s = s;
        addm_s2 = s2;
      }), () |)
    | Inr pl ->
      let Zeta.Steel.LogEntry.Types.Mkuninterpreted _ b = pl in
      (| Zeta.Formats.Aux.Log_entry_hdr.Le_payload_AddMApp ({
        addmapp_s = s;
        addmapp_s2 = s2;
      }), FStar.Bytes.hide b |)
    end
  | Zeta.Steel.LogEntry.Types.AddB s t tid p _ ->
    begin match Ghost.reveal p with
    | Inl (k, v) ->
      (| Zeta.Formats.Aux.Log_entry_hdr.Le_payload_AddB ({
        addb_k = synth_key_recip k;
        addb_v = synth_mval_value_recip v;
        addb_s = s;
        addb_t = t;
        addb_tid = tid;
      }), () |)
    | Inr pl ->
      let Zeta.Steel.LogEntry.Types.Mkuninterpreted _ b = pl in
      (| Zeta.Formats.Aux.Log_entry_hdr.Le_payload_AddBApp ({
        addbapp_s = s;
        addbapp_t = t;
        addbapp_tid = tid;
      }), FStar.Bytes.hide b |)
    end
  | Zeta.Steel.LogEntry.Types.RunApp 
      (Zeta.Steel.LogEntry.Types.MkrunApp_payload
        rpl
        (Zeta.Steel.LogEntry.Types.Mkuninterpreted _ pl))
    ->
    (| Zeta.Formats.Aux.Log_entry_hdr.Le_payload_RunApp rpl, FStar.Bytes.hide pl |)
  | Zeta.Steel.LogEntry.Types.NextEpoch ->
    (| Zeta.Formats.Aux.Log_entry_hdr.Le_payload_NextEpoch (), () |)
  | Zeta.Steel.LogEntry.Types.VerifyEpoch ->
    (| Zeta.Formats.Aux.Log_entry_hdr.Le_payload_VerifyEpoch (), () |)
  | 
    Zeta.Steel.LogEntry.Types.EvictM
      (Zeta.Steel.LogEntry.Types.MkevictM_payload s s2)
    ->
    (| Zeta.Formats.Aux.Log_entry_hdr.Le_payload_EvictM ({
        evictm_s = s; evictm_s2 = s2
    }), () |)
  | Zeta.Steel.LogEntry.Types.EvictB
      (Zeta.Steel.LogEntry.Types.MkevictB_payload s t)
    ->
    (| Zeta.Formats.Aux.Log_entry_hdr.Le_payload_EvictB ({
        evictb_s = s; evictb_t = t;
    }), () |)
  | Zeta.Steel.LogEntry.Types.EvictBM
      (Zeta.Steel.LogEntry.Types.MkevictBM_payload s s2 t)
    ->
    (| Zeta.Formats.Aux.Log_entry_hdr.Le_payload_EvictBM ({
      evictbm_s = s; evictbm_s2 = s2; evictbm_t = t;
    }), () |)

#push-options "--ifuel 8"
let serialize_ifthenelse_param : LowParse.Spec.IfThenElse.serialize_ifthenelse_param parse_ifthenelse_param =
  LowParse.Spec.IfThenElse.Mkserialize_ifthenelse_param
    Zeta.Formats.Aux.Log_entry_hdr.log_entry_hdr_serializer
    payload_serializer'
    synth_log_entry_false_recip
    (fun x -> ())
#pop-options

let synth_log_entry_recip
  (relate_payload: bool)
  (p: Zeta.Steel.LogEntry.Types.log_entry0 relate_payload)
: GTot (LowParse.Spec.Combinators.parse_filter_refine (parse_log_entry_filter relate_payload))
= match p with
  | Zeta.Steel.LogEntry.Types.AddM s s' p r0 ->
    let r = match Ghost.reveal p with
    | Inl _ -> r0
    | Inr u ->
      if relate_payload
      then Zeta.Steel.LogEntry.Types.dummy_record
      else r0
    in
    Zeta.Steel.LogEntry.Types.AddM s s' p r
  | Zeta.Steel.LogEntry.Types.AddB s ts tid p r0 ->
    let r = match Ghost.reveal p with
    | Inl _ -> r0
    | Inr u ->
      if relate_payload
      then Zeta.Steel.LogEntry.Types.dummy_record
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

let serialize_log_entry relate_payload =
  LowParse.Spec.Combinators.serialize_synth
    _
    (synth_log_entry relate_payload)
    (LowParse.Spec.Combinators.serialize_filter (LowParse.Spec.IfThenElse.serialize_ifthenelse serialize_ifthenelse_param) (parse_log_entry_filter relate_payload))
    (synth_log_entry_recip relate_payload)
    ()
