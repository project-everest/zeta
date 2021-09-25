module Zeta.SeqConsistent

open FStar.Seq
open Zeta.Interleave
open Zeta.App
open Zeta.AppSimulate
open Zeta.AppSimulate.Helper
open Zeta.Key
open Zeta.GenKey
open Zeta.Record
open Zeta.GenericVerifier
open Zeta.High.Verifier
open Zeta.EAC
open Zeta.Generic.Interleave
open Zeta.High.Interleave

module V = Zeta.GenericVerifier
module T = Zeta.Generic.Thread
module G = Zeta.Generic.Global
module GI = Zeta.Generic.Interleave
module HV = Zeta.High.Verifier
module I = Zeta.Interleave
module S = FStar.Seq
module SA = Zeta.SeqAux
module EAC=Zeta.EAC
module MSD = Zeta.MultiSetHashDomain


(* TODO: Move to Generic.Interleave *)
let lemma_appfn_calls_interleave (#app #n:_) (il: verifiable_log app n)
  : Lemma (ensures (let fcrs_il = app_fcrs_il il in
                    let gl = to_glog il in
                    s_seq fcrs_il = G.app_fcrs gl))
          [SMTPat (app_fcrs_il il)]
  = admit()

(* TODO: Move to Generic.Interleave *)
let app_fcrs_empty (#app #n:_) (il: verifiable_log app n)
  : Lemma (ensures (length il = 0 ==> S.length (app_fcrs il) = 0))
  = admit()

(* TODO: Move to Generic.Interleave *)
let appfn_calls_snoc (#app #n:_) (il: verifiable_log app n {length il > 0})
  : Lemma (ensures (let i = length il - 1 in
                    let e = index il i in
                    let il' = prefix il i in
                    let cr = app_fcrs il in
                    let cr' = app_fcrs il' in
                    match e with
                    | RunApp _ _ _ -> cr == SA.append1 cr' (to_app_fcr il i)
                    | _ -> cr == cr'))
  = admit()

let eac_app_state (#app #n:_) (il: eac_log app n) (ak: app_key app.adm)
  = let gk = AppK ak in
    AppV?.v (eac_value gk il)

let to_fc (#app #n:_) (il: eac_log app n) (i: seq_index il {RunApp? (index il i)})
  : appfn_call app
  = let App (RunApp fid_c arg_c _) inp_c = mk_vlog_entry_ext il i in
    { fid_c; arg_c ; inp_c }

let eac_implies_appfn_success (#app #n:_) (il: eac_log app n) (i: seq_index il {RunApp? (index il i)})
  : Lemma (ensures (correct (to_fc il i)))
          [SMTPat (to_fc il i)]
  = let open Zeta.BinTree in
    eac_state_transition Root il i

let eac_app_prop (#app #n:_) (il: eac_log app n)
  = let fcrs = app_fcrs il in
    let fcs = app_fcs fcrs in
    (* the results are valid meaning the output corresponds to the input records *)
    valid_call_result fcrs /\
    (* the app state as recorded by eac values is the same as the simulation state *)
    post_state fcs == eac_app_state il

(* TODO: Move to AppSimulate.Helper *)
let empty_call_result_valid (#app) (rs: seq (appfn_call_res app))
  : Lemma (ensures (S.length rs = 0 ==> valid_call_result rs))
  = admit()

let eac_app_prop_empty (#app #n:_) (il: eac_log app n)
  : Lemma (ensures (length il = 0 ==> eac_app_prop il))
  = if length il = 0 then (
      app_fcrs_empty il;
      empty_call_result_valid (app_fcrs il);

      let aux (ak:key app)
        : Lemma (ensures (True))
        = admit()
      in
      admit()
    )

let eac_app_state_key_snoc (#app #n:_) (il: eac_log app n {length il > 0}) (ak: app_key app.adm)
  : Lemma (ensures (let i = length il - 1 in
                    let e = index il i in
                    let il' = prefix il i in
                    match e with
                    | RunApp f p ss ->
                      let fc = to_fc il i in
                      if fc `refs_comp` ak then
                        eac_app_state il ak = write fc ak
                      else
                        eac_app_state il ak = eac_app_state il' ak
                    | _ -> eac_app_state il ak = eac_app_state il' ak))
  = admit()

let eac_app_state_nonapp_snoc (#app #n:_) (il: eac_log app n {length il > 0})
  : Lemma (ensures (let i = length il - 1 in
                    let il' = prefix il i in
                    not (RunApp? (index il i)) ==>
                    eac_app_state il == eac_app_state il'))
  = let i = length il - 1 in
    let il' = prefix il i in
    let e = index il i in
    if not (RunApp? e) then (
      let aux (ak:_)
        : Lemma (ensures (eac_app_state il ak = eac_app_state il' ak))
        = eac_app_state_key_snoc il ak
      in
      FStar.Classical.forall_intro aux;
      assert(app_state_feq (eac_app_state il) (eac_app_state il'))
    )

let eac_implies_app_prop_snoc (#app #n:_) (il: eac_log app n {length il > 0})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     eac_app_prop il'))
          (ensures eac_app_prop il)
  = let i = length il - 1 in
    let il' = prefix il i in
    let fcrs = app_fcrs il in
    let fcrs' = app_fcrs il' in
    let e = index il i in
    appfn_calls_snoc il;
    eac_app_state_nonapp_snoc il;

    match e with
    | RunApp f p ss -> admit()
    | _ -> ()

let rec eac_implies_app_prop (#app #n:_) (il: eac_log app n)
  : Lemma (ensures (eac_app_prop il))
          (decreases (length il))
  = eac_app_prop_empty il;
    if length il > 0 then (
      let i = length il - 1 in
      let il' = prefix il i in
      eac_implies_app_prop il';
      eac_implies_app_prop_snoc il
    )

let interleaving_implies_interleave (#a #n:_) (il: interleaving a n)
  : Lemma (ensures (interleave (i_seq il) (s_seq il)))
  = let is = i_seq il in
    let ss = s_seq il in
    FStar.Classical.exists_intro (fun il -> i_seq il = is /\ s_seq il = ss) il

let lemma_eac_implies_appfn_calls_seq_consistent (#app #n:_) (il: eac_log app n)
  : Lemma (ensures (let gl = to_glog il in
                    Zeta.AppSimulate.seq_consistent (G.app_fcrs gl)))
  = let fcrs_il = app_fcrs_il il in
    let fcrs = i_seq fcrs_il in
    let fcrss = s_seq fcrs_il in
    interleaving_implies_interleave fcrs_il;
    assert(interleave fcrs fcrss);
    eac_implies_app_prop il;
    assert(valid_call_result fcrs);
    FStar.Classical.exists_intro (fun is -> interleave #(appfn_call_res app) is fcrss) fcrs
