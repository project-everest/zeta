module Zeta.High.TSLog

open Zeta.App
open Zeta.Time
open Zeta.Generic.Interleave
open Zeta.Generic.TSLog
open Zeta.High.Verifier
open Zeta.High.Interleave

module S = FStar.Seq
module T = Zeta.Generic.TSLog

let its_log (app: app_params)
  = T.its_log (high_verifier_spec app)

let is_neac_before_epoch (#app #n:_) (ep: epoch) (itsl: its_log app n)
  = not (is_eac itsl) &&
      (let bi = eac_boundary itsl in
       let t = clock itsl bi in
       t.e <= ep)

let neac_before_epoch (app n:_) (ep: epoch)
  = itsl: its_log app n { is_neac_before_epoch ep itsl }
