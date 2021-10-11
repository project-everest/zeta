module Zeta.Intermediate.Global

open Zeta.SSeq
open Zeta.Time
open Zeta.Intermediate.Verifier
open Zeta.Intermediate.Logs
open Zeta.Generic.Global

module IT = Zeta.Intermediate.Thread

let verifiable_log (vcfg:_)
  = Zeta.Generic.Global.verifiable_log (int_verifier_spec vcfg)

let ms_verifiable_log (vcfg:_) (epmax: epoch)
  = gl: verifiable_log vcfg {aems_equal_upto epmax gl}

let to_logk_entry (#vcfg:_) (gl: verifiable_log vcfg) (i: sseq_index gl)
  : logK_entry vcfg.app
  = let t,j = i in
    let tl = index gl t in
    IT.to_logk_entry tl j

