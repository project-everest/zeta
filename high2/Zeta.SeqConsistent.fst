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

let eac_value_snoc (#app #n:_) = Zeta.High.Merkle.eac_value_snoc_appkey #app #n

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

let eac_value_is_eac_state_value (#app #n:_) (il: eac_log app n) (ak: app_key app.adm)
  : Lemma (ensures (let gk = AppK ak in
                    let es = eac_state_of_genkey gk il in
                    match es with
                    | EACInStore _ _ gv -> eac_value gk il = gv
                    | EACEvictedMerkle _ gv -> eac_value gk il = gv
                    | EACEvictedBlum _ gv _ _ -> eac_value gk il = gv
                    | EACInit -> eac_value gk il = init_value gk))
  = let gk = AppK ak in
    let bk = to_base_key gk in
    let es = eac_state_of_genkey gk il in
    match es with
    | EACInit -> eac_value_init_state_is_init il gk
    | EACInStore _ _ gv ->
      eac_app_state_value_is_stored_value il gk;
      eac_value_is_stored_value il gk (stored_tid bk il)
    | _ -> eac_value_is_evicted_value il gk

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
      let fcrs = app_fcrs il in
      let fcs = app_fcs fcrs in

      (* app call sequence is empty *)
      app_fcrs_empty il;
      assert(S.length fcs = 0);

      (* an empty call sequence is valid *)
      empty_call_result_valid (app_fcrs il);

      (* the app state per the simulator - the initial state where everything is null *)
      let sta = post_state fcs in

      (* the eac state of the keys *)
      let ste = eac_app_state il in

      let aux (ak:app_key app.adm)
        : Lemma (ensures (ste ak = sta ak))
        = lemma_init_value_null fcs ak;
          let bk = to_base_key (AppK ak) in
          eac_state_empty bk il;
          eac_value_init (AppK ak) il
      in
      FStar.Classical.forall_intro aux;
      assert(app_state_feq ste sta)
    )

let app_refs_is_log_entry_refs
  (#app #n:_)
  (il: eac_log app n)
  (i: seq_index il)
  (ak: app_key app.adm)
  : Lemma (requires (RunApp? (index il i)))
          (ensures (let gk = AppK ak in
                    let bk = to_base_key gk in
                    let fc = to_fc il i in
                    let e = index il i in
                    let RunApp _ _ ss = e in
                    fc `refs` ak ==>
                    e `refs_key` bk /\ index_mem bk ss = refkey_idx fc ak))
  = let RunApp _ _ refkeys = index il i in

    let fc = to_fc il i in
    if fc `refs_comp` ak then
      (* the param index of ak *)
      let idx = refkey_idx fc ak in

      (* the key at location idx - we don't bk' = bk yet *)
      let bk' = S.index refkeys idx in

      (* relate the eac states before and after i for key bk' - the solver figures out the rest ... *)
      eac_state_transition bk' il i

let log_entry_refs_is_app_refs
  (#app #n:_)
  (il: eac_log app n)
  (i: seq_index il)
  (ak: app_key app.adm)
  : Lemma (requires (RunApp? (index il i)))
          (ensures (let gk = AppK ak in
                    let bk = to_base_key gk in
                    let fc = to_fc il i in
                    let e = index il i in
                    let il' = prefix il i in
                    let il'' = prefix il (i+1) in
                    let RunApp _ _ ss = e in
                    e `refs_key` bk ==>
                    ~ (fc `refs` ak) ==>
                    eac_state_of_genkey gk il' = EACInit /\
                    eac_state_of_genkey gk il'' = EACInit))
  = let gk = AppK ak in
    let bk = to_base_key gk in
    let e = index il i in
    let RunApp _ _ refkeys = e in
    let fc = to_fc il i in
    eac_state_transition bk il i;

    if e `refs_key` bk && not (fc `refs_comp` ak) then
      let idx = index_mem bk refkeys in
      let ak',av' = S.index fc.inp_c idx in
      let es' = eac_state_of_key_pre bk il i in
      match es' with
      | EACInStore _ gk' _ ->
        assert(AppK ak' = gk');
        if ak' = ak then refs_witness fc ak idx

let eac_app_state_key_snoc_refs_key
  (#app #n:_)
  (il: eac_log app n {length il > 0}) (ak: app_key app.adm)
  : Lemma (requires (let i = length il - 1 in
                     RunApp? (index il i) /\
                     to_fc il i `refs` ak))
          (ensures (let i = length il - 1 in
                    eac_app_state il ak = write (to_fc il i) ak))
  = let i = length il - 1 in
    let gk = AppK ak in
    let bk = to_base_key gk in
    eac_state_snoc bk il;
    app_refs_is_log_entry_refs il i ak;
    eac_app_state_value_is_stored_value il gk;
    eac_value_is_stored_value il gk (stored_tid bk il)

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
  = let i = length il - 1 in
    let e = index il i in
    let ee = mk_vlog_entry_ext il i in
    let il' = prefix il i in
    let gk = AppK ak in
    let bk = to_base_key gk in
    eac_value_snoc gk il;
    eac_state_snoc bk il;
    SA.lemma_fullprefix_equal il;

    match e with
    | RunApp f p ss ->
      app_refs_is_log_entry_refs il i ak;
      log_entry_refs_is_app_refs il i ak;
      let fc = to_fc il i in
      if fc `refs_comp` ak then
        eac_app_state_key_snoc_refs_key il ak
      else if e `refs_key` bk then (
        eac_value_init_state_is_init il gk;
        eac_value_init_state_is_init il' gk
      )
    | _ -> ()

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

let eac_implies_input_consistent_key
  (#app #n:_)
  (il: eac_log app n)
  (i: seq_index il)
  (ak: app_key app.adm)
  : Lemma (requires (RunApp? (index il i)))
          (ensures (let il' = prefix il i in
                    let fc = to_fc il i in
                    let st = eac_app_state il' in
                    fc `refs` ak ==>
                    refkey_inp_val fc ak = st ak))
  = let gk = AppK ak in
    let bk = to_base_key gk in
    let il' = prefix il i in
    let fc = to_fc il i in
    app_refs_is_log_entry_refs il i ak;
    eac_state_transition bk il i;
    if fc `refs_comp` ak then
      eac_value_is_eac_state_value il' ak

let eac_implies_input_consistent
  (#app #n:_)
  (il: eac_log app n)
  (i: seq_index il)
  : Lemma (requires (RunApp? (index il i)))
          (ensures (let il' = prefix il i in
                    let fc = to_fc il i in
                    let st = eac_app_state il' in
                    input_consistent fc st))
  = let fc = to_fc il i in
    let il' = prefix il i in
    let st = eac_app_state il' in

  let aux (ak: app_key app.adm)
    : Lemma (ensures (fc `refs` ak ==> refkey_inp_val fc ak = st ak))
    = eac_implies_input_consistent_key il i ak
  in
  FStar.Classical.forall_intro aux

let eac_app_state_app_snoc (#app #n:_) (il: eac_log app n {length il > 0})
  : Lemma (requires (let i = length il - 1  in
                     let il' = prefix il i in
                     RunApp? (index il i) /\ eac_app_prop il'))
          (ensures (let fcs = app_fcs (app_fcrs il) in
                    valid fcs /\
                    eac_app_state il == post_state fcs))
  = let i = length il - 1 in
    let fcr = to_app_fcr il i in
    let il' = prefix il i in

    let fcrs = app_fcrs il in
    let fcs = app_fcs fcrs in
    let fcrs' = app_fcrs il' in
    let fcs' = app_fcs fcrs' in
    let fc = to_fc il i in

    appfn_calls_snoc il;
    ext_app_records_is_stored_val il i;
    assert(fcrs == SA.append1 fcrs' fcr);
    assume(fcs = SA.append1 fcs' fc);
    SA.lemma_prefix1_append fcs' fc;

    let st' = post_state fcs' in
    assert(st' == eac_app_state il');
    eac_implies_input_consistent il i;
    correct_succeeds_if_input_consistent fc st';
    assert(valid fcs);

    let sts = post_state fcs in
    let ste = eac_app_state il in
    let aux (ak: app_key app.adm)
      : Lemma (ensures (sts ak = ste ak))
      = app_refs_is_log_entry_refs il i ak;
        lemma_post_state fc st' ak;
        eac_app_state_key_snoc il ak
    in
    FStar.Classical.forall_intro aux;
    assert(app_state_feq sts ste)

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
