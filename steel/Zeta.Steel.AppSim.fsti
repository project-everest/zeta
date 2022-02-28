module Zeta.Steel.AppSim

open Zeta.Steel.ThreadStateModel
open Zeta.Steel.Rel
open Zeta.Steel.LogRel
open Zeta.Steel.StoreRel
open Zeta.Steel.ThreadRelDef

module A = Zeta.App
module AS = Zeta.AppSimulate
module AT = Zeta.Steel.ApplicationTypes
module GV = Zeta.GenericVerifier
module IV = Zeta.Intermediate.Verifier
module T = Zeta.Steel.FormatsManual

val runapp_simulation (tsm: s_thread_state) (i_tsm: i_thread_state) (se: s_log_entry) (ie: i_log_entry)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_log_entry se ie /\
                     T.RunApp? se /\ not tsm.failed))
          (ensures (let T.RunApp p = se in
                    let tsm_ = runapp tsm p in
                    let i_tsm_ = GV.verify_step ie i_tsm in
                    (not tsm_.failed) ==> related_tsm tsm_ i_tsm_))

let runapp_out_t
  = let open AT in
    fid:A.appfn_id app &
    app_args fid &
    app_records fid &
    app_result fid

let valid_runapp_param (tsm: s_thread_state) (se: s_log_entry)
  = let open T in
    RunApp? se /\
    (let RunApp p = se in
     let tsm_ = runapp tsm p in
     not tsm_.failed)

val runapp_output (tsm: s_thread_state)
                  (se: s_log_entry {valid_runapp_param tsm se})
  : GTot (o:runapp_out_t {let T.RunApp p = se in
                          let tsm_ = runapp tsm p in
                          tsm_.app_results = Seq.snoc tsm.app_results o})

let related_output (so: runapp_out_t) (io: AS.appfn_call_res app)
  = let (| fid, arg, inp, res  |) = so in
    let open AS in
    fid = io.fid_cr /\
    arg = io.arg_cr /\
    inp = io.inp_cr /\
    res = io.res_cr

val runapp_output_related (tsm: s_thread_state)
                          (i_tsm: i_thread_state)
                          (se: s_log_entry)
                          (ie: i_log_entry)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_log_entry se ie /\
                     not tsm.failed /\
                     valid_runapp_param tsm se))
          (ensures (let res = runapp_output tsm se in
                    let i_tsm_ = GV.verify_step ie i_tsm in
                    GV.is_appfn ie /\
                    i_tsm_.IV.valid /\
                    (let i_res = GV.appfn_result ie i_tsm in
                     related_output res i_res)))
