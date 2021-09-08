module Zeta.High.Global

open Zeta.App
open Zeta.Time
open Zeta.Generic.Global
open Zeta.High.Verifier

let vlog (app:app_params) = Zeta.Generic.Global.vlog (high_verifier_spec app)

let verifiable_log (app:_)
  = Zeta.Generic.Global.verifiable_log (high_verifier_spec app)

let gen_sseq (app: app_params) = Zeta.Generic.Global.gen_sseq (high_verifier_spec app)

let ms_verifiable_log (app: app_params) (ep: epoch)
  = Zeta.Generic.Global.ms_verifiable_log #(high_verifier_spec app) ep
