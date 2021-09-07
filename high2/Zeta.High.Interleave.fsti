module Zeta.High.Interleave

open FStar.Seq
open Zeta.App
open Zeta.Generic.Interleave
open Zeta.High.Verifier
open Zeta.EAC

module V = Zeta.GenericVerifier
module T = Zeta.Generic.Thread
module G = Zeta.Generic.Global
module GI = Zeta.Generic.Interleave
module I = Zeta.Interleave
module S = FStar.Seq
module SA = Zeta.SeqAux
module IF = Zeta.IdxFn
module SF = Zeta.SIdxFn
module EAC=Zeta.EAC

let ilog (app: app_params) = Zeta.Generic.Interleave.ilog (high_verifier_spec app)

let gen_seq (app: app_params)
  = Zeta.Generic.Interleave.gen_seq (high_verifier_spec app)

let verifiable_log (app:_) (n:nat)
  = il:ilog app n {verifiable il}

val mk_vlog_entry_ext (#app: app_params) (#n:nat)
  : IF.idxfn_t (gen_seq app n) (vlog_entry_ext app)

let vlog_ext_of_il_log (#app: app_params) (#n:nat)
  (il: verifiable_log app n)
  : seq (vlog_entry_ext app)
  = IF.map mk_vlog_entry_ext il

val is_eac (#app #n:_) (il: verifiable_log app n)
  : b:bool{b <==> eac (vlog_ext_of_il_log il)}

let eac_log (app: app_params) (n:nat) = il: verifiable_log app n {is_eac il}

let neac_log (app: app_params) (n:nat) = il: verifiable_log app n {~ (is_eac il)}

val eac_boundary (#app #n:_) (il: neac_log app n)
  : (i: seq_index il{is_eac (prefix il i) /\
                     ~ (is_eac (prefix il (i+1)))})

val lemma_eac_implies_prefix_eac (#app #n:_) (il: eac_log app n) (i: nat{i <= S.length il})
  : Lemma (ensures (is_eac (prefix il i)))

#push-options "--z3rlimit_factor 3"
// TODO: why (high_verifier_spec app).app == app is so hard to infer?
let appfn_calls (#app #n:_) (il: eac_log app n)
  : seq (Zeta.AppSimulate.appfn_call_res app)
  = GI.appfn_calls il
#pop-options

val lemma_eac_implies_appfn_valid (#app #n:_) (il: eac_log app n)
  : Lemma (ensures (Zeta.AppSimulate.valid_call_result (appfn_calls il)))
