module Zeta.High.SeqConsistent

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

val lemma_eac_implies_appfn_calls_seq_consistent (#app #n:_) (il: eac_log app n)
  : Lemma (ensures (let gl = to_glog il in
                    Zeta.AppSimulate.seq_consistent (G.app_fcrs gl)))
