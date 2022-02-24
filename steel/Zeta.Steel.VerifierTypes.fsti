module Zeta.Steel.VerifierTypes

open Zeta.Steel.ApplicationTypes
open Zeta.Steel.FormatsManual
open Steel.ST.Util
module M = Zeta.Steel.ThreadStateModel

#push-options "--ide_id_info_off"

[@@CAbstractStruct]
val thread_state_t
  : Type0

val thread_id (t:thread_state_t)
  : tid

val thread_state_inv_core (t:thread_state_t)
                          ([@@@smt_fallback] m:M.thread_state_model)
  : vprop

let tsm_entries_invariant (tsm:M.thread_state_model) =
    not tsm.failed ==>
    tsm == M.verify_model (M.init_thread_state_model tsm.thread_id)
                          tsm.processed_entries

val thread_state_inv (t:thread_state_t)
                     ([@@@smt_fallback] m:M.thread_state_model)
  : vprop

val intro_thread_state_inv (#o:_)
                           (#tsm:M.thread_state_model)
                           (t:thread_state_t)
  : STGhost unit o
    (thread_state_inv_core t tsm)
    (fun _ -> thread_state_inv t tsm)
    (requires
      thread_id t == tsm.thread_id /\
      tsm_entries_invariant tsm)
    (ensures fun _ -> True)

val elim_thread_state_inv (#o:_) (#tsm:M.thread_state_model) (t:thread_state_t)
  : STGhost unit o
    (thread_state_inv t tsm)
    (fun _ -> thread_state_inv_core t tsm)
    (requires True)
    (ensures fun _ ->
      thread_id t == tsm.thread_id /\
      tsm_entries_invariant tsm)

let extract_tsm_entries_invariant (#o:_) (#tsm:M.thread_state_model) (t:thread_state_t)
  : STGhost unit o
    (thread_state_inv t tsm)
    (fun _ -> thread_state_inv t tsm)
    (requires True)
    (ensures fun _ ->
      thread_id t == tsm.thread_id /\
      tsm_entries_invariant tsm)
  = elim_thread_state_inv t;
    intro_thread_state_inv t
