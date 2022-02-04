module Zeta.Formats.LogEntry

let needs_payload
  (x: Zeta.Formats.Aux.Log_entry_hdr.log_entry_hdr)
: Tot bool
= let open Zeta.Formats.Aux.Log_entry_hdr in
  match x with
  | Le_payload_RunApp _
    -> true
  | _ -> false

let payload (needs_payload: bool) : Tot Type0 =
  if needs_payload
  then LowParse.Spec.Bytes.parse_bounded_vlbytes_t 0 2147483647
  else unit

inline_for_extraction
let payload_len (pl: Ghost.erased (payload true)) : Tot Type0 =
  (x: FStar.UInt32.t { x == FStar.Bytes.len pl })

let payload_parser (needs_payload: bool) : Tot (k: LP.parser_kind & LP.parser k (payload needs_payload)) =
  if needs_payload
  then (| _, LowParse.Spec.Bytes.parse_bounded_vlbytes 0 2147483647 |)
  else (| _, LowParse.Spec.Combinators.parse_empty |)

open Zeta.Formats.Aux.Addm_payload
open Zeta.Formats.Aux.Addb_payload
open Zeta.Formats.Aux.Evictm_payload
open Zeta.Formats.Aux.Evictb_payload
open Zeta.Formats.Aux.Evictbm_payload
open Zeta.Formats.Synth

let synth_log_entry_false
  (x: Zeta.Formats.Aux.Log_entry_hdr.log_entry_hdr {needs_payload x == false })
: Tot Zeta.Steel.LogEntry.Types.log_entry
= match x with
  | Zeta.Formats.Aux.Log_entry_hdr.Le_payload_AddM apl ->
    let r = synth_record apl.addm_r in
    Zeta.Steel.LogEntry.Types.AddM
      apl.addm_s
      apl.addm_s2
      r
  | Zeta.Formats.Aux.Log_entry_hdr.Le_payload_AddB apl ->
    let r = synth_record apl.addb_r in
    Zeta.Steel.LogEntry.Types.AddB
      apl.addb_s
      apl.addb_t
      apl.addb_tid
      r
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

let synth_log_entry_true
  (x: Zeta.Formats.Aux.Log_entry_hdr.log_entry_hdr { needs_payload x == true })
  (pl: Ghost.erased (payload true))
  (pl_len: payload_len pl)
: Tot Zeta.Steel.LogEntry.Types.log_entry
= match x with
  | Zeta.Formats.Aux.Log_entry_hdr.Le_payload_RunApp rpl ->
    Zeta.Steel.LogEntry.Types.RunApp
      (Zeta.Steel.LogEntry.Types.MkrunApp_payload
        rpl
        (Zeta.Steel.LogEntry.Types.Mkuninterpreted pl_len (FStar.Bytes.reveal pl))
      )

let synth_log_entry
  (x: Zeta.Formats.Aux.Log_entry_hdr.log_entry_hdr)
  (pl: payload (needs_payload x))
: Tot Zeta.Steel.LogEntry.Types.log_entry
= if needs_payload x
  then synth_log_entry_true x pl (FStar.Bytes.len pl)
  else synth_log_entry_false x

let parse_ifthenelse_param =
  LowParse.Spec.IfThenElse.Mkparse_ifthenelse_param
    _ _
    Zeta.Formats.Aux.Log_entry_hdr.log_entry_hdr_parser
    needs_payload
    payload
    payload_parser
    _
    synth_log_entry
    (fun t1 x1 t2 x2 -> ())

let parse_log_entry_kind = LowParse.Spec.IfThenElse.parse_ifthenelse_kind parse_ifthenelse_param

let parse_log_entry =
  LowParse.Spec.IfThenElse.parse_ifthenelse parse_ifthenelse_param

let payload_serializer (needs_payload: bool) : Tot (LP.serializer (dsnd (payload_parser needs_payload))) =
  if needs_payload
  then LowParse.Spec.Bytes.serialize_bounded_vlbytes 0 2147483647
  else LowParse.Spec.Combinators.serialize_empty

let payload_serializer' (needs_payload: bool) : Tot (LP.serializer (dsnd (parse_ifthenelse_param.LowParse.Spec.IfThenElse.parse_ifthenelse_payload_parser needs_payload))) = payload_serializer needs_payload

let synth_log_entry_recip_hdr
  (y: Zeta.Steel.LogEntry.Types.log_entry)
: Tot Zeta.Formats.Aux.Log_entry_hdr.log_entry_hdr
= match y with
  | Zeta.Steel.LogEntry.Types.AddM s s2 r ->
    let r0 = synth_record_recip r in
      Zeta.Formats.Aux.Log_entry_hdr.Le_payload_AddM ({
        addm_r = r0;
        addm_s = s;
        addm_s2 = s2;
      })
  | Zeta.Steel.LogEntry.Types.AddB s t tid r ->
    let r0 = synth_record_recip r in
      Zeta.Formats.Aux.Log_entry_hdr.Le_payload_AddB ({
        addb_r = r0;
        addb_s = s;
        addb_t = t;
        addb_tid = tid;
      })
  | Zeta.Steel.LogEntry.Types.RunApp 
      (Zeta.Steel.LogEntry.Types.MkrunApp_payload
        rpl
        (Zeta.Steel.LogEntry.Types.Mkuninterpreted _ pl))
    ->
    Zeta.Formats.Aux.Log_entry_hdr.Le_payload_RunApp rpl
  | Zeta.Steel.LogEntry.Types.NextEpoch ->
    Zeta.Formats.Aux.Log_entry_hdr.Le_payload_NextEpoch ()
  | Zeta.Steel.LogEntry.Types.VerifyEpoch ->
    Zeta.Formats.Aux.Log_entry_hdr.Le_payload_VerifyEpoch ()
  | 
    Zeta.Steel.LogEntry.Types.EvictM
      (Zeta.Steel.LogEntry.Types.MkevictM_payload s s2)
    ->
    Zeta.Formats.Aux.Log_entry_hdr.Le_payload_EvictM ({
        evictm_s = s; evictm_s2 = s2
    })
  | Zeta.Steel.LogEntry.Types.EvictB
      (Zeta.Steel.LogEntry.Types.MkevictB_payload s t)
    ->
    Zeta.Formats.Aux.Log_entry_hdr.Le_payload_EvictB ({
        evictb_s = s; evictb_t = t;
    })
  | Zeta.Steel.LogEntry.Types.EvictBM
      (Zeta.Steel.LogEntry.Types.MkevictBM_payload s s2 t)
    ->
    Zeta.Formats.Aux.Log_entry_hdr.Le_payload_EvictBM ({
      evictbm_s = s; evictbm_s2 = s2; evictbm_t = t;
    })

let synth_log_entry_recip_pl
  (y: Zeta.Steel.LogEntry.Types.log_entry)
: GTot (payload (needs_payload (synth_log_entry_recip_hdr y)))
= match y with
  | Zeta.Steel.LogEntry.Types.RunApp 
      (Zeta.Steel.LogEntry.Types.MkrunApp_payload
        rpl
        (Zeta.Steel.LogEntry.Types.Mkuninterpreted _ pl))
    -> FStar.Bytes.hide pl
  | _ -> ()

let synth_log_entry_recip
  (y: Zeta.Steel.LogEntry.Types.log_entry)
: GTot (t: Zeta.Formats.Aux.Log_entry_hdr.log_entry_hdr & payload (needs_payload t))
= (| synth_log_entry_recip_hdr y, synth_log_entry_recip_pl y |)

#push-options "--ifuel 8"
let serialize_ifthenelse_param : LowParse.Spec.IfThenElse.serialize_ifthenelse_param parse_ifthenelse_param =
  LowParse.Spec.IfThenElse.Mkserialize_ifthenelse_param
    Zeta.Formats.Aux.Log_entry_hdr.log_entry_hdr_serializer
    payload_serializer'
    synth_log_entry_recip
    (fun x -> ())
#pop-options

let serialize_log_entry =
  LowParse.Spec.IfThenElse.serialize_ifthenelse serialize_ifthenelse_param
