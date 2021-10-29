module Veritas.MultiThreadSimulation

module G = FStar.Ghost
module VSeq = Veritas.SeqAux
module Spec = Veritas.Verifier
module IntT = Veritas.Intermediate.Thread
module I = Veritas.Intermediate.Verify
module IntG = Veritas.Intermediate.Global
module Mwc = Veritas.Steel.MainWorkerChannel
module SSim = Veritas.SingleThreadSimulation
module TSM = Veritas.ThreadStateModel
module Formats = Veritas.Epoch
module SteelModel = Veritas.Steel.VerifierModel
module MSH = Veritas.MultiSetHashDomain

let verify_step_model_implies_lift_some vcfg (tsm:TSM.thread_state_model)
  (e:Formats.vlog_entry)
  : Lemma
      (requires not (SteelModel.verify_step_model tsm e).TSM.model_failed)
      (ensures Some? (TSM.lift_log_entry #vcfg e))
  = admit ()

#push-options "--fuel 1 --ifuel 0"
let rec verify_model_implies_lift_some vcfg (tsm:TSM.thread_state_model) (s:Seq.seq (Formats.vlog_entry))
  : Lemma
      (requires not (SteelModel.verify_model tsm s).TSM.model_failed)
      (ensures Some? (TSM.lift_log_entries #vcfg s))
      (decreases Seq.length s)
      [SMTPat (SteelModel.verify_model tsm s); SMTPat (TSM.lift_log_entries #vcfg s)]
  = let n = Seq.length s in
    if n = 0 then ()
    else begin
      let prefix = VSeq.prefix s (n - 1) in
      let nth = Seq.index s (n - 1) in
      let tsm_prefix = SteelModel.verify_model tsm prefix in
      verify_model_implies_lift_some vcfg tsm prefix;
      verify_step_model_implies_lift_some vcfg tsm_prefix nth
    end
#pop-options

noeq
type epoch_hash_entry = {
  t_id : Spec.thread_id;
  e_id : Formats.epoch_id;
  entries : Seq.seq Formats.vlog_entry;
  hadd : TSM.model_hash;
  hevict : h:TSM.model_hash{
    let tsm = SteelModel.verify_model (TSM.initial_thread_state_model t_id) entries in
    not tsm.TSM.model_failed /\
    tsm.TSM.model_hadd == hadd /\
    tsm.TSM.model_hevict == h}
}

type epoch_hash_entries = s:Seq.seq epoch_hash_entry{
  forall (i:nat{i < Seq.length s}).
    let eh = Seq.index s i in
    eh.t_id == i
}

let lift_epoch_log_entries vcfg (eh:epoch_hash_entry) =
  Some?.v (TSM.lift_log_entries #vcfg eh.entries)

let ehs_to_verifiable_log vcfg (s:epoch_hash_entries) : IntG.verifiable_log vcfg =
  VSeq.map (lift_epoch_log_entries vcfg) s

module HA = Veritas.Steel.HashAccumulator

let rec ehs_combine_hadds (s:epoch_hash_entries)
  : Tot TSM.model_hash (decreases Seq.length s) =

  let n = Seq.length s in
  if n = 0
  then HA.initial_hash
  else let eh = Seq.index s (n - 1) in
       let s = VSeq.prefix s (n - 1) in
       let h = ehs_combine_hadds s in
       HA.aggregate_hash_value h eh.hadd

let rec ehs_combine_hevicts (s:epoch_hash_entries)
  : Tot TSM.model_hash (decreases Seq.length s) =

  let n = Seq.length s in
  if n = 0
  then HA.initial_hash
  else let eh = Seq.index s (n - 1) in
       let s = VSeq.prefix s (n - 1) in
       let h = ehs_combine_hevicts s in
       HA.aggregate_hash_value h eh.hevict

#push-options "--fuel 1 --z3rlimit 20"
let rec ehs_hashes_match_vlog_hashes vcfg (s:epoch_hash_entries)
  : Lemma
      (ensures
        TSM.related_hashes (ehs_combine_hadds s)
                           (IntG.hadd (ehs_to_verifiable_log vcfg s)) /\
        TSM.related_hashes (ehs_combine_hevicts s)
                           (IntG.hevict (ehs_to_verifiable_log vcfg s)))
      (decreases Seq.length s)
  = admit()
  // let n = Seq.length s in
  //   if n > 0 then begin
  //     ehs_hashes_match_vlog_hashes vcfg (VSeq.prefix s (n - 1));
  //     VSeq.lemma_map_prefix (lift_epoch_log_entries vcfg) s (n - 1)
  //   end
#pop-options

let ehs_to_hash_verifiable_log vcfg
  (s:epoch_hash_entries{ehs_combine_hadds s == ehs_combine_hevicts s})
  : IntG.hash_verifiable_log vcfg 
  = admit();
    ehs_hashes_match_vlog_hashes vcfg s;
    ehs_to_verifiable_log vcfg s
