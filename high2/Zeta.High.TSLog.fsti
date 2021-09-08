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

let neac_before_epoch (app n:_) (ep: epoch)
  = itsl: its_log app n {not (is_eac (prefix_within_epoch ep itsl))}

val neac_before_epoch_implies_neac (#app #n:_) (ep: epoch) (itsl: neac_before_epoch app n ep)
  : Lemma (ensures (not (is_eac itsl)))
          [SMTPat (prefix_within_epoch ep itsl)]
