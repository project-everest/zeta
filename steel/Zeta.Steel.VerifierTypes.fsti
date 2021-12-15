module Zeta.Steel.VerifierTypes

open Zeta.Steel.ApplicationTypes
open Zeta.Steel.FormatsManual
open Steel.ST.Util
module M = Zeta.Steel.ThreadStateModel

#push-options "--ide_id_info_off"

val thread_state_t
  : Type0

val thread_id (t:thread_state_t)
  : tid

val thread_state_inv (t:thread_state_t) ([@@@smt_fallback] m:M.thread_state_model)
  : vprop

val elim_thread_state_inv (#o:_) (#tsm:M.thread_state_model) (t:thread_state_t)
  : STGhost unit o
    (thread_state_inv t tsm)
    (fun _ -> thread_state_inv t tsm)
    (requires True)
    (ensures fun _ ->
      tsm == M.verify_model (M.init_thread_state_model (thread_id t))
                            tsm.processed_entries)
