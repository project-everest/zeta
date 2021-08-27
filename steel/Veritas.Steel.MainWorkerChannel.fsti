module Veritas.Steel.MainWorkerChannel

module G = FStar.Ghost

open Steel.Effect

module TSM = Veritas.ThreadStateModel
module VTypes = Veritas.Formats.Types
module Model = Veritas.Steel.VerifierModel
module Awc = Veritas.Steel.ApplicationWorkerChannel


val epoch_id : Type0

val initial_thread_state_model (id:epoch_id)
  : tsm:TSM.thread_state_model{tsm.TSM.model_failed == false}

noeq
type epoch_hash_entry (c:G.erased Awc.ch) = {
  e_id : epoch_id;
  entries : s:G.erased (Seq.seq VTypes.vlog_entry){exists n. Awc.sent_s c s n};
  hadd : TSM.model_hash;
  hevict : h:TSM.model_hash{
    let tsm = Model.verify_model (initial_thread_state_model e_id) entries in
    not tsm.TSM.model_failed      /\
    tsm.TSM.model_hadd == hadd    /\
    tsm.TSM.model_hevict == h};
}

val ch : Type0

val reader (c:ch) : vprop
val writer (c:ch) : vprop

val sent (#a_ch:G.erased Awc.ch) (c:ch) (eh:epoch_hash_entry a_ch) : prop

val write (#a_ch:G.erased Awc.ch) (c:ch) (eh:epoch_hash_entry a_ch)
  : SteelT bool
      (writer c)
      (fun b -> pure (b ==> sent c eh) `star` writer c)

val read (#a_ch:G.erased Awc.ch) (c:ch)
  : SteelT (epoch_hash_entry a_ch)
      (reader c)
      (fun eh -> pure (sent c eh) `star` reader c)
