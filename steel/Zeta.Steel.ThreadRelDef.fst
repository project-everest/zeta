module Zeta.Steel.ThreadRelDef

(* This module defines related_tsm - the thread state (tsm) is related at steel layer and intermediate
 * layer. *)

open Zeta.Steel.Rel
open Zeta.Steel.StoreRel

module IV = Zeta.Intermediate.Verifier

let related_tsm (s: s_thread_state) (i: i_thread_state)
  = (not s.failed = i.IV.valid) /\
    (i.IV.valid ==>
     ((related_tid s.thread_id i.IV.tid) /\
      (related_timestamp s.clock i.IV.clock) /\
      (related_base_key s.last_evict_key i.IV.last_evict_key) /\
      (related_store s.store i.IV.st)))
