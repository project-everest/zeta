module Zeta.Steel.ThreadSim

open Zeta.Steel.ThreadStateModel
open Zeta.Steel.Rel
open Zeta.Steel.LogRel
open Zeta.Steel.StoreRel
open Zeta.Steel.ThreadRelDef
open Zeta.Steel.AddMRel

module GV = Zeta.GenericVerifier
module IV = Zeta.Intermediate.Verifier
module T = Zeta.Steel.FormatsManual
module LT = Zeta.Steel.LogEntry.Types

val addm_simulation (tsm: s_thread_state) (i_tsm: i_thread_state) (se: s_log_entry) (ie: i_log_entry)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_log_entry se ie /\
                     LT.AddM? se /\ not tsm.failed))
          (ensures (let LT.AddM s s' r = se in
                    let GV.AddM ir is is' = ie in
                    let tsm_ = vaddm tsm s s' r in
                    let i_tsm_ = IV.addm ir is is' i_tsm in
                    (not tsm_.failed) ==> related_tsm tsm_ i_tsm_))

val addb_simulation (tsm: s_thread_state) (i_tsm: i_thread_state) (se: s_log_entry) (ie: i_log_entry)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_log_entry se ie /\
                     LT.AddB? se /\ not tsm.failed))
          (ensures (let LT.AddB s t tid r = se in
                    let GV.AddB i_r i_s i_t i_tid = ie in
                    let tsm_ = vaddb tsm s t tid r  in
                    let i_tsm_ = IV.addb i_r i_s i_t i_tid i_tsm in
                    (not tsm_.failed) ==> related_tsm tsm_ i_tsm_))

val evictm_simulation (tsm: s_thread_state) (i_tsm: i_thread_state) (se: s_log_entry) (ie: i_log_entry)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_log_entry se ie /\
                     LT.EvictM? se /\ not tsm.failed))
          (ensures (let LT.EvictM p = se in
                    let GV.EvictM i_s i_s' = ie in
                    let tsm_ = vevictm tsm p.s p.s_  in
                    let i_tsm_ = IV.evictm i_s i_s' i_tsm in
                    (not tsm_.failed) ==> related_tsm tsm_ i_tsm_))

val evictb_simulation (tsm: s_thread_state) (i_tsm: i_thread_state) (se: s_log_entry) (ie: i_log_entry)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_log_entry se ie /\
                     LT.EvictB? se /\ not tsm.failed))
          (ensures (let LT.EvictB p = se in
                    let GV.EvictB i_s i_t = ie in
                    let tsm_ = vevictb tsm p.s p.t in
                    let i_tsm_ = IV.evictb i_s i_t i_tsm in
                    (not tsm_.failed) ==> related_tsm tsm_ i_tsm_))

val evictbm_simulation (tsm: s_thread_state) (i_tsm: i_thread_state) (se: s_log_entry) (ie: i_log_entry)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_log_entry se ie /\
                     LT.EvictBM? se /\ not tsm.failed))
          (ensures (let LT.EvictBM p = se in
                    let GV.EvictBM i_s i_s' i_t = ie in
                    let tsm_ = vevictbm tsm p.s p.s_ p.t in
                    let i_tsm_ = IV.evictbm i_s i_s' i_t i_tsm in
                    (not tsm_.failed) ==> related_tsm tsm_ i_tsm_))

val nextepoch_simulation (tsm: s_thread_state) (i_tsm: i_thread_state) (se: s_log_entry) (ie: i_log_entry)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_log_entry se ie /\
                     LT.NextEpoch? se /\ not tsm.failed))
          (ensures (let tsm_ = nextepoch tsm in
                    let i_tsm_ = IV.nextepoch i_tsm in
                    (not tsm_.failed) ==> related_tsm tsm_ i_tsm_))

val verifyepoch_simulation (tsm: s_thread_state) (i_tsm: i_thread_state) (se: s_log_entry) (ie: i_log_entry)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_log_entry se ie /\
                     LT.VerifyEpoch? se /\ not tsm.failed))
          (ensures (let tsm_ = verifyepoch tsm in
                    let i_tsm_ = IV.verifyepoch i_tsm in
                    (not tsm_.failed) ==> related_tsm tsm_ i_tsm_))
