module Zeta.Steel.LogRel

(* This module sets up the relationship between steel log-related concepts and the corresponding spec level ones *)

open Zeta.App
open Zeta.Steel.KeyUtils
open Zeta.Steel.Rel

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module L = FStar.List.Tot
module GK = Zeta.GenKey
module K = Zeta.Key
module M = Zeta.Merkle
module GV = Zeta.GenericVerifier
module IL = Zeta.Intermediate.Logs
module IV = Zeta.Intermediate.Verifier
module AT = Zeta.Steel.ApplicationTypes
module T = Zeta.Steel.FormatsManual
module TSM = Zeta.Steel.ThreadStateModel
module SA = Zeta.SeqAux

let valid_app_record (b: T.uninterpreted)
  = match ApplicationRecord.spec_parser_app_record b.ebytes with
    | None -> False
    | Some _ -> True

let parse_app_record_local (b: T.uninterpreted {valid_app_record b})
  : GTot s_record
  = let open AT in
    let open T in
    match ApplicationRecord.spec_parser_app_record b.ebytes with
    | Some ((k,v), _) -> (ApplicationKey k, DValue v)

let valid_app_fid (sfid: s_fid)
  = Map.contains app.tbl sfid

let lif_app_fid (sfid: s_fid {valid_app_fid sfid})
  : i_fid
  = sfid

let valid_app_param (fid: i_fid) (b: T.uninterpreted)
  = let open T in
    let open AT in
    match spec_app_parser fid b.ebytes with
    | None -> False
    | Some ((arg, slots), len) ->
      len == U32.v b.len /\
      (forall i. valid_slot (Seq.index slots i))

let parse_arg (fid: i_fid) (b: T.uninterpreted {valid_app_param fid b})
  : GTot (appfn_arg fid)
  = let open T in
    let open AT in
    match spec_app_parser fid b.ebytes with
    | Some ((arg, _), _) -> arg

let parse_slots (fid: _) (b: T.uninterpreted {valid_app_param fid b})
  : GTot (Seq.seq s_slot_id)
  = let open T in
    let open AT in
    match spec_app_parser fid b.ebytes with
    | Some ((_,slots),_) -> slots

let valid_log_entry (e: s_log_entry)
  = let open Zeta.Steel.LogEntry.Types in
    match e with
    | AddM s s' r -> valid_slot s /\ valid_slot s' /\ True
    | AddB s ts tid r -> valid_slot s /\ True
    | EvictM e -> valid_slot e.s /\ valid_slot e.s_ /\ True
    | EvictB e -> valid_slot e.s /\ True
    | EvictBM e -> valid_slot e.s /\ valid_slot e.s_ /\ True
    | RunApp e -> valid_app_fid e.fid /\
                 valid_app_param e.fid e.rest /\
                 True
    | _ -> True

let related_log_entry (se: s_log_entry) (ie: i_log_entry)
  = let open Zeta.Steel.LogEntry.Types in
    match se, ie with
    | AddM s s' r, GV.AddM i_r i_s i_s'  ->
      related_record r i_r /\
      related_slot s i_s /\
      related_slot s' i_s'
    | AddB s t tid r, GV.AddB i_r i_s i_t i_tid ->
      related_record r i_r /\
      related_slot s i_s /\
      related_timestamp t i_t /\
      related_tid tid i_tid
    | EvictM p, GV.EvictM s s' ->
      related_slot p.s s /\
      related_slot p.s_ s'
    | EvictB p, GV.EvictB s t ->
      related_slot p.s s /\
      related_timestamp p.t t
    | EvictBM p, GV.EvictBM s s' t ->
      related_slot p.s s /\
      related_slot p.s_ s' /\
      related_timestamp p.t t
    | NextEpoch, GV.NextEpoch ->
      True
    | VerifyEpoch, GV.VerifyEpoch ->
      True
    | RunApp p, GV.RunApp f arg is ->
      p.fid = f /\
      valid_app_param f p.rest /\
      parse_arg f p.rest = arg /\
      (let ss = parse_slots f p.rest in
       Seq.length ss = Seq.length is /\
       (forall i. related_slot (Seq.index ss i) (Seq.index is i)))
    | _ -> False

val lift_log_entry (se: s_log_entry {valid_log_entry se})
  : GTot (ie: i_log_entry { related_log_entry se ie })

let valid_log (l: s_log)
  = forall i. (valid_log_entry (Seq.index l i))

let related_log (sl: s_log) (il: i_log)
  = Seq.length sl = Seq.length il /\
    (forall i. related_log_entry (Seq.index sl i) (Seq.index il i))

val lift_log (sl: s_log {valid_log sl})
  : GTot (il:i_log {related_log sl il})

val lift_log_snoc (sl: s_log {valid_log sl}) (se: s_log_entry {valid_log_entry se})
  : Lemma (requires (let sl_ = Seq.snoc sl se in
                     valid_log sl_))
          (ensures (let il = lift_log sl in
                    let ie = lift_log_entry se in
                    let sl_ = Seq.snoc sl se in
                    let il_ = lift_log sl_ in
                    let i = Seq.length sl in
                    il_ == Seq.snoc il ie /\
                    Seq.index il_ i = ie))

val prefix_of_valid_valid (l: s_log {valid_log l}) (i: nat{ i <= Seq.length l})
  : Lemma (ensures (let l' = SA.prefix l i in
                    valid_log l'))
          [SMTPat (SA.prefix l i)]

val lift_prefix_commute (l: s_log {valid_log l}) (i: nat{ i <= Seq.length l})
  : Lemma (ensures (lift_log (SA.prefix l i) == SA.prefix (lift_log l) i))
