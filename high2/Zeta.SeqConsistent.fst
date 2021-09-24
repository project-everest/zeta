module Zeta.SeqConsistent

open FStar.Seq
open Zeta.Interleave
open Zeta.App
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

open Zeta.AppSimulate
open Zeta.AppSimulate.Helper

let lemma_appfn_calls_interleave (#app #n:_) (il: verifiable_log app n)
  : Lemma (ensures (let cril = appfn_calls_il il in
                    let gl = to_glog il in
                    s_seq cril = G.appfn_calls gl))
          [SMTPat (appfn_calls_il il)]
  = admit()

let appfn_calls_empty (#app #n:_) (il: verifiable_log app n)
  : Lemma (ensures (length il = 0 ==> S.length (appfn_calls il) = 0))
  = admit()

let appfn_calls_snoc (#app #n:_) (il: verifiable_log app n {length il > 0})
  : Lemma (ensures (let i = length il - 1 in
                    let e = index il i in
                    let il' = prefix il i in
                    let cr = appfn_calls il in
                    let cr' = appfn_calls il' in
                    match e with
                    | RunApp _ _ _ -> cr == SA.append1 cr' (to_appfn_call_res il i)
                    | _ -> cr == cr'))
  = admit()

let empty_call_result_valid (#app) (rs: seq (appfn_call_res app))
  : Lemma (ensures (S.length rs = 0 ==> valid_call_result rs))
  = admit()

let eac_implies_appfn_valid_empty (#app #n:_) (il: eac_log app n)
  : Lemma (ensures (length il = 0 ==> valid_call_result (appfn_calls il)))
  = if length il = 0 then (
      appfn_calls_empty il;
      empty_call_result_valid (appfn_calls il)
    )

let eac_implies_appfn_valid_snoc (#app #n:_) (il: eac_log app n {length il > 0})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     valid_call_result (appfn_calls il')))
          (ensures (valid_call_result (appfn_calls il)))
  = let i = length il - 1 in
    let il' = prefix il i in
    let cr = appfn_calls il in
    let cr' = appfn_calls il' in
    let e = index il i in
    appfn_calls_snoc il;

    match e with
    | RunApp f p ss -> admit()
    | _ -> ()

let rec eac_implies_appfn_valid (#app #n:_) (il: eac_log app n)
  : Lemma (ensures (let cr = appfn_calls il in
                    valid_call_result cr))
          (decreases (length il))
  = eac_implies_appfn_valid_empty il;
    if length il > 0 then (
      let i = length il - 1 in
      let il' = prefix il i in
      eac_implies_appfn_valid il';
      eac_implies_appfn_valid_snoc il
    )

let interleaving_implies_interleave (#a #n:_) (il: interleaving a n)
  : Lemma (ensures (interleave (i_seq il) (s_seq il)))
  = let is = i_seq il in
    let ss = s_seq il in
    FStar.Classical.exists_intro (fun il -> i_seq il = is /\ s_seq il = ss) il

let lemma_eac_implies_appfn_calls_seq_consistent (#app #n:_) (il: eac_log app n)
  : Lemma (ensures (let gl = to_glog il in
                    Zeta.AppSimulate.seq_consistent (G.appfn_calls gl)))
  = let cr_il = appfn_calls_il il in
    let crs = i_seq cr_il in
    let crss = s_seq cr_il in
    interleaving_implies_interleave cr_il;
    assert(interleave crs crss);
    eac_implies_appfn_valid il;
    assert(valid_call_result crs);
    FStar.Classical.exists_intro (fun is -> interleave #(appfn_call_res app) is crss) crs
