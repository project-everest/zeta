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
module Formats = Veritas.Formats.Types
module SteelModel = Veritas.Steel.VerifierModel
module MSH = Veritas.MultiSetHashDomain

let tsm_to_vtls_initial vcfg (t_id:Spec.thread_id) (e_id:Mwc.epoch_id)
  : Lemma (SSim.tsm_to_vtls vcfg (Mwc.initial_thread_state_model e_id) ==
           I.init_thread_state t_id (IntT.init_store vcfg t_id))
          [SMTPat (SSim.tsm_to_vtls vcfg (Mwc.initial_thread_state_model e_id));
           SMTPat (I.init_thread_state t_id (IntT.init_store vcfg t_id))]
  = admit ()

let verify_model_implies_lift vcfg (tsm:TSM.thread_state_model) (s:Seq.seq (Formats.vlog_entry))
  : Lemma
      (requires not (SteelModel.verify_model tsm s).TSM.model_failed)
      (ensures Some? (TSM.lift_log_entries #vcfg s))
      [SMTPat (SteelModel.verify_model tsm s); SMTPat (TSM.lift_log_entries #vcfg s)]
  = admit ()

noeq
type epoch_hash_entry = {
  e_id : Mwc.epoch_id;
  entries : Seq.seq Formats.vlog_entry;
  hadd : TSM.model_hash;
  hevict : h:TSM.model_hash{
    let tsm = SteelModel.verify_model (Mwc.initial_thread_state_model e_id) entries in
    not tsm.TSM.model_failed /\
    tsm.TSM.model_hadd == hadd /\
    tsm.TSM.model_hevict == h}
}

let ehs_to_verifiable_log vcfg (s:Seq.seq epoch_hash_entry)
  : IntG.verifiable_log vcfg =
  
  VSeq.map (fun eh -> Some?.v (TSM.lift_log_entries #vcfg eh.entries)) s

let rec ehs_combine_hadds (s:Seq.seq epoch_hash_entry)
  : Tot TSM.model_hash (decreases Seq.length s) =

  let n = Seq.length s in
  if n = 0
  then MSH.empty_hash_value
  else let eh = Seq.index s (n - 1) in
       let s = VSeq.prefix s (n - 1) in
       let h = ehs_combine_hadds s in
       Veritas.MultiSetHash.ms_hashfn_agg h eh.hadd

let rec ehs_combine_hevicts (s:Seq.seq epoch_hash_entry)
  : Tot TSM.model_hash (decreases Seq.length s) =

  let n = Seq.length s in
  if n = 0
  then MSH.empty_hash_value
  else let eh = Seq.index s (n - 1) in
       let s = VSeq.prefix s (n - 1) in
       let h = ehs_combine_hevicts s in
       Veritas.MultiSetHash.ms_hashfn_agg h eh.hevict

#push-options "--fuel 1"
let rec ehs_hashes_match_vlog_hashes vcfg (s:Seq.seq epoch_hash_entry)
  : Lemma
      (ensures
        ehs_combine_hadds s == IntG.hadd (ehs_to_verifiable_log vcfg s) /\
        ehs_combine_hevicts s == IntG.hevict (ehs_to_verifiable_log vcfg s))
      (decreases Seq.length s)
  = let n = Seq.length s in
    if n = 0 then ()
    else ehs_hashes_match_vlog_hashes vcfg (VSeq.prefix s (n - 1))
#pop-options

let ehs_to_hash_verifiable_log vcfg
  (s:Seq.seq epoch_hash_entry{ehs_combine_hadds s == ehs_combine_hevicts s})
  : IntG.hash_verifiable_log vcfg =
  
  ehs_hashes_match_vlog_hashes vcfg s;
  ehs_to_verifiable_log vcfg s
