module Zeta.High.Correctness

open Zeta.App
open Zeta.Time
open Zeta.AppSimulate
open Zeta.High.Verifier
open Zeta.Generic.Global
open Zeta.Generic.Interleave
open Zeta.Generic.TSLog
open Zeta.High.Global
open Zeta.High.Interleave
open Zeta.HashCollision

module I = Zeta.Interleave
module G = Zeta.Generic.Global
module HG = Zeta.High.Global

let lemma_verifier_correct
  (#app:_)
  (epmax: epoch)
  (gl: HG.ms_verifiable_log app epmax{~ (seq_consistent (appfn_calls_within_ep epmax gl))})
  : hash_collision app
  = (* sequence of sequence of app fn calls and results *)
    let app_calls_ss = appfn_calls_within_ep epmax gl in

    (* interleaving of gl ordered by time of each log entry *)
    let itsl = create gl in

    (* prefix upto epoch epmax *)
    let itsl_ep = prefix_within_epoch epmax itsl in
    lemma_appfn_calls_within_epoch epmax itsl;
    assert(G.appfn_calls (to_glog itsl_ep) = app_calls_ss);

    lemma_add_evict_set_identical_glog epmax itsl;
    assert(aems_equal_upto epmax itsl);

    if is_eac itsl_ep then (
      (* is_eac itsl_ep ==> this sequence is sequentially consistent *)
      lemma_eac_implies_appfn_calls_seq_consistent itsl_ep;
      assert(seq_consistent (G.appfn_calls (to_glog itsl_ep)));

      hash_collision_contra app
    )
    else
      Zeta.High.Verifier.EAC.lemma_neac_implies_hash_collision epmax itsl
