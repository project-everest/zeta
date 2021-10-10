module Zeta.Intermediate.Global

open Zeta.SSeq
open Zeta.Intermediate.Verifier
open Zeta.Intermediate.Logs
open Zeta.Generic.Global

module IT = Zeta.Intermediate.Thread

let verifiable_log (vcfg:_)
  = Zeta.Generic.Global.verifiable_log (int_verifier_spec vcfg)

let to_logk_entry (#vcfg:_) (gl: verifiable_log vcfg) (i: sseq_index gl)
  : logK_entry vcfg.app
  = let t,j = i in
    let tl = index gl t in
    IT.to_logk_entry tl j

