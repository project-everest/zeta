module Zeta.High.TSLog

open Zeta.App
open Zeta.Time
open Zeta.Generic.TSLog
open Zeta.High.Verifier
open Zeta.High.Interleave

module T = Zeta.Generic.TSLog

let its_log (app: app_params)
  = T.its_log (high_verifier_spec app)

let neac_before_epoch (app n:_) (ep: epoch)
  = itsl: its_log app n {not (is_eac (prefix_within_epoch ep itsl))}
