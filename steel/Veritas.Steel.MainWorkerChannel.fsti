module Veritas.Steel.MainWorkerChannel

module G = FStar.Ghost

open Steel.Effect

module TSM = Veritas.ThreadStateModel
module Formats = Veritas.Formats.Types
module Model = Veritas.Steel.VerifierModel
module Awc = Veritas.Steel.ApplicationWorkerChannel

// noeq
// type epoch_hash_entry (c:G.erased Awc.ch) = {
//   e_id : Formats.epoch_id;
//   entries : s:G.erased (Seq.seq Formats.vlog_entry){exists n. Awc.sent_s c s n};
//   hadd : TSM.model_hash;
//   hevict : h:TSM.model_hash{
//     let tsm = Model.verify_model (TSM.initial_thread_state_model e_id) entries in
//     not tsm.TSM.model_failed      /\
//     tsm.TSM.model_hadd == hadd    /\
//     tsm.TSM.model_hevict == h};
// }

val ch : Type0

val reader (c:ch) : vprop
val writer (c:ch) : vprop

val sent (#a_ch:G.erased Awc.ch) (c:ch) (eh:Formats.epoch_hash_entry) : prop

val write (#a_ch:G.erased Awc.ch) (c:ch) (eh:Formats.epoch_hash_entry)
  : SteelT bool
      (writer c)
      (fun b -> pure (b ==> sent #a_ch c eh) `star` writer c)

val read (#a_ch:G.erased Awc.ch) (c:ch)
  : SteelT Formats.epoch_hash_entry
      (reader c)
      (fun eh -> pure (sent #a_ch c eh) `star` reader c)
