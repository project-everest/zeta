module Zeta.Intermediate.Global

open Zeta.SSeq
open Zeta.Time
open Zeta.Intermediate.Verifier
open Zeta.Intermediate.Logs
open Zeta.Generic.Global

module S = FStar.Seq
module IT = Zeta.Intermediate.Thread
module HG = Zeta.High.Global

let verifiable_log (vcfg:_)
  = Zeta.Generic.Global.verifiable_log (int_verifier_spec vcfg)

let ms_verifiable_log (vcfg:_) (epmax: epoch)
  = gl: verifiable_log vcfg {aems_equal_upto epmax gl}

let to_logk_entry (#vcfg:_) (gl: verifiable_log vcfg) (i: sseq_index gl)
  : logK_entry vcfg.app
  = let t,j = i in
    let tl = index gl t in
    IT.to_logk_entry tl j

let global_rel (#vcfg:_) (gl: verifiable_log vcfg) (glk: HG.verifiable_log vcfg.app)
  = S.length gl = S.length glk /\
    (forall t. IT.thread_rel (index gl t) (index glk t))

val global_rel_implies_appfn_identical (#vcfg:_) (gls: verifiable_log vcfg) (glk: _{global_rel gls glk})
  : Lemma (ensures (app_fcrs gls = app_fcrs glk))
