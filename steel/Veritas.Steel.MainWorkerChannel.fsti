module Veritas.Steel.MainWorkerChannel

module G = FStar.Ghost

open Steel.Effect

module TSM = Veritas.ThreadStateModel
module Formats = Veritas.Epoch
module Model = Veritas.Steel.VerifierModel
module Awc = Veritas.Steel.ApplicationWorkerChannel

val ch : Type0

val reader (c:ch) (a_ch:Awc.ch) : vprop
val writer (c:ch) (a_ch:Awc.ch) : vprop

val sent (c:ch) (a_ch:Awc.ch) (eh:Formats.epoch_hash_entry) : prop

let valid_epoch_hash_entry (a_ch:Awc.ch) (eh:Formats.epoch_hash_entry) : prop =
  let open Formats in
  let open TSM in
  exists (es:Seq.seq vlog_entry).
    (exists (n:nat). Awc.sent_s a_ch es n) /\
    (let tsm = Model.verify_model (initial_thread_state_model (UInt16.v eh.t_id)) es in
     not tsm.model_failed /\
     TSM.related_hashes tsm.model_hadd (TSM.bitvec_of_u256 eh.hadd) /\
     TSM.related_hashes tsm.model_hevict (TSM.bitvec_of_u256 eh.hevict))

val write (#a_ch:G.erased Awc.ch)
  (c:ch)
  (eh:Formats.epoch_hash_entry{valid_epoch_hash_entry a_ch eh})
  : SteelT bool
      (writer c a_ch)
      (fun b -> pure (b ==> sent c a_ch eh) `star` writer c a_ch)

val read (#a_ch:G.erased Awc.ch) (c:ch)
  : SteelT (eh:Formats.epoch_hash_entry{valid_epoch_hash_entry a_ch eh})
      (reader c a_ch)
      (fun eh -> pure (sent c a_ch eh) `star` reader c a_ch)
