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
  = match T.spec_parser_app_record b.ebytes with
    | None -> False
    | Some _ -> True

let parse_app_record_local (b: T.uninterpreted {valid_app_record b})
  : GTot s_record
  = let open AT in
    let open T in
    match spec_parser_app_record b.ebytes with
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
  = let open T in
    match e with
    | AddM e -> valid_record (e.k, MValue e.v) /\
                valid_slot e.s /\
                valid_slot e.s'
    | AddB e -> valid_record (e.k, MValue e.v) /\
                valid_slot e.s
    | EvictM e -> valid_slot e.s /\ valid_slot e.s'
    | EvictB e -> valid_slot e.s /\ True
    | EvictBM e -> valid_slot e.s /\ valid_slot e.s'
    | AddMApp e -> valid_slot e.s /\ valid_slot e.s' /\
                   valid_app_record e.rest
    | AddBApp e -> valid_slot e.s /\
                   valid_app_record e.rest
    | RunApp e -> valid_app_fid e.fid /\
                  valid_app_param e.fid e.rest
    | _ -> True

let related_log_entry (se: s_log_entry) (ie: i_log_entry)
  = let open T in
    match se, ie with
    | AddM p, GV.AddM (k,v) s s'  ->
      related_key p.k k /\
      related_val (MValue p.v) v /\
      related_slot p.s s /\
      related_slot p.s' s'
    | AddB p, GV.AddB (k,v) s t j ->
      related_key p.k k /\
      related_val (MValue p.v) v /\
      related_slot p.s s /\
      related_timestamp p.t t /\
      related_tid p.tid j
    | EvictM p, GV.EvictM s s' ->
      related_slot p.s s /\
      related_slot p.s' s'
    | EvictB p, GV.EvictB s t ->
      related_slot p.s s /\
      related_timestamp p.t t
    | EvictBM p, GV.EvictBM s s' t ->
      related_slot p.s s /\
      related_slot p.s' s' /\
      related_timestamp p.t t
    | NextEpoch _, GV.NextEpoch ->
      True
    | VerifyEpoch _, GV.VerifyEpoch ->
      True
    | AddMApp p, GV.AddM r s s' ->
      valid_app_record p.rest /\
      related_record (parse_app_record_local p.rest) r /\
      related_slot p.s s /\
      related_slot p.s' s'
    | AddBApp p, GV.AddB r s t j ->
      valid_app_record p.rest /\
      related_record (parse_app_record_local p.rest) r /\
      related_slot p.s s /\
      related_timestamp p.t t /\
      related_tid p.tid j
    | RunApp p, GV.RunApp f arg is ->
      p.fid = f /\
      valid_app_param f p.rest /\
      parse_arg f p.rest = arg /\
      (let ss = parse_slots f p.rest in
       Seq.length ss = Seq.length is /\
       (forall i. related_slot (Seq.index ss i) (Seq.index is i)))
    | _ -> False

val lift_log_entry (se: s_log_entry {valid_log_entry se})
  : ie: i_log_entry { related_log_entry se ie }

let valid_log (l: s_log)
  = forall i. (valid_log_entry (Seq.index l i))

let related_log (sl: s_log) (il: i_log)
  = Seq.length sl = Seq.length il /\
    (forall i. related_log_entry (Seq.index sl i) (Seq.index il i))

val lift_log (sl: s_log {valid_log sl})
  : il:i_log {related_log sl il}

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
