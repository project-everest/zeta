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

val addm_simulation (tsm: s_thread_state) (i_tsm: i_thread_state) (se: s_log_entry) (ie: i_log_entry)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_log_entry se ie /\
                     T.AddM? se /\ not tsm.failed))
          (ensures (let T.AddM p = se in
                    let GV.AddM ir is is' = ie in
                    let tsm_ = vaddm tsm p.s p.s' (Inl (p.k, p.v)) in
                    let i_tsm_ = IV.addm ir is is' i_tsm in
                    (not tsm_.failed) ==> related_tsm tsm_ i_tsm_))

val addmapp_simulation (tsm: s_thread_state) (i_tsm: i_thread_state) (se: s_log_entry) (ie: i_log_entry)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_log_entry se ie /\
                     T.AddMApp? se /\ not tsm.failed))
          (ensures (let T.AddMApp p = se in
                    let GV.AddM ir is is' = ie in
                    let tsm_ = vaddm tsm p.s p.s' (Inr p.rest) in
                    let i_tsm_ = IV.addm ir is is' i_tsm in
                    (not tsm_.failed) ==> related_tsm tsm_ i_tsm_))

val addb_simulation (tsm: s_thread_state) (i_tsm: i_thread_state) (se: s_log_entry) (ie: i_log_entry)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_log_entry se ie /\
                     T.AddB? se /\ not tsm.failed))
          (ensures (let T.AddB p = se in
                    let GV.AddB i_r i_s i_t i_tid = ie in
                    let tsm_ = vaddb tsm p.s p.t p.tid (Inl (p.k, p.v))  in
                    let i_tsm_ = IV.addb i_r i_s i_t i_tid i_tsm in
                    (not tsm_.failed) ==> related_tsm tsm_ i_tsm_))

val addbapp_simulation (tsm: s_thread_state) (i_tsm: i_thread_state) (se: s_log_entry) (ie: i_log_entry)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_log_entry se ie /\
                     T.AddBApp? se /\ not tsm.failed))
          (ensures (let T.AddBApp p = se in
                    let GV.AddB i_r i_s i_t i_tid = ie in
                    let tsm_ = vaddb tsm p.s p.t p.tid (Inr p.rest)  in
                    let i_tsm_ = IV.addb i_r i_s i_t i_tid i_tsm in
                    (not tsm_.failed) ==> related_tsm tsm_ i_tsm_))

val evictm_simulation (tsm: s_thread_state) (i_tsm: i_thread_state) (se: s_log_entry) (ie: i_log_entry)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_log_entry se ie /\
                     T.EvictM? se /\ not tsm.failed))
          (ensures (let T.EvictM p = se in
                    let GV.EvictM i_s i_s' = ie in
                    let tsm_ = vevictm tsm p.s p.s'  in
                    let i_tsm_ = IV.evictm i_s i_s' i_tsm in
                    (not tsm_.failed) ==> related_tsm tsm_ i_tsm_))

val evictb_simulation (tsm: s_thread_state) (i_tsm: i_thread_state) (se: s_log_entry) (ie: i_log_entry)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_log_entry se ie /\
                     T.EvictB? se /\ not tsm.failed))
          (ensures (let T.EvictB p = se in
                    let GV.EvictB i_s i_t = ie in
                    let tsm_ = vevictb tsm p.s p.t in
                    let i_tsm_ = IV.evictb i_s i_t i_tsm in
                    (not tsm_.failed) ==> related_tsm tsm_ i_tsm_))

val evictbm_simulation (tsm: s_thread_state) (i_tsm: i_thread_state) (se: s_log_entry) (ie: i_log_entry)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_log_entry se ie /\
                     T.EvictBM? se /\ not tsm.failed))
          (ensures (let T.EvictBM p = se in
                    let GV.EvictBM i_s i_s' i_t = ie in
                    let tsm_ = vevictbm tsm p.s p.s' p.t in
                    let i_tsm_ = IV.evictbm i_s i_s' i_t i_tsm in
                    (not tsm_.failed) ==> related_tsm tsm_ i_tsm_))

val nextepoch_simulation (tsm: s_thread_state) (i_tsm: i_thread_state) (se: s_log_entry) (ie: i_log_entry)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_log_entry se ie /\
                     T.NextEpoch? se /\ not tsm.failed))
          (ensures (let tsm_ = nextepoch tsm in
                    let i_tsm_ = IV.nextepoch i_tsm in
                    (not tsm_.failed) ==> related_tsm tsm_ i_tsm_))

val verifyepoch_simulation (tsm: s_thread_state) (i_tsm: i_thread_state) (se: s_log_entry) (ie: i_log_entry)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_log_entry se ie /\
                     T.VerifyEpoch? se /\ not tsm.failed))
          (ensures (let tsm_ = verifyepoch tsm in
                    let i_tsm_ = IV.verifyepoch i_tsm in
                    (not tsm_.failed) ==> related_tsm tsm_ i_tsm_))
