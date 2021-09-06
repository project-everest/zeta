module Zeta.High.Interleave

open Zeta.App
open Zeta.Generic.Interleave
open Zeta.High.Verifier

let ilog (app: app_params) = Zeta.Generic.Interleave.ilog (high_verifier_spec app)

