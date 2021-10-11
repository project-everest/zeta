module Zeta.Intermediate.Correctness

open Zeta.App
open Zeta.AppSimulate
open Zeta.Time
open Zeta.HashCollision
open Zeta.Generic.Global
open Zeta.Generic.Interleave
open Zeta.Generic.TSLog
open Zeta.Generic.Blum
open Zeta.High.Interleave
open Zeta.Intermediate.Global
open Zeta.Intermediate.Interleave
open Zeta.Intermediate.TSLog

module S = FStar.Seq
module GG = Zeta.Generic.Global

(*
 * A bunch of properties we use in the induction step:
 *    (a) the intermediate verifiers all satisfy the store invariant
 *    (b) the intermediate and spec level verifiers states correspond to one-another (related)
 *    (c) the spec level log is time sorted (b and c imply that the spec log has type its_log)
 *    (d) the spec level log is evict-add-consistent
 * TODO: rename this
 *)
#push-options "--fuel 0 --ifuel 1 --query_stats"

let induction_props #vcfg (ils: its_log vcfg) =
  let ilk = to_logk ils in
  spec_rel ils /\
  is_eac ilk

#pop-options

let induction_props_or_hash_collision #vcfg (ils: its_log vcfg) =
  o:option (hash_collision vcfg.app) {Some? o \/ induction_props ils}

#push-options "--fuel 0 --ifuel 1 --query_stats"

let lemma_empty_implies_induction_props #vcfg (il: verifiable_log vcfg)
  : Lemma (ensures (length il = 0 ==> induction_props il))
  = if length il = 0 then (
      lemma_empty_implies_spec_rel il;
      empty_implies_eac (to_logk il)
    )

let induction_props_snoc
  (#vcfg:_)
  (epmax: epoch)
  (il: its_log vcfg {aems_equal_upto epmax il})
  (i: seq_index il {let il' = prefix il i in
                    (clock il i).e <= epmax /\
                    induction_props il'})
  : induction_props_or_hash_collision (prefix il (i+1))
  = admit()


#pop-options

#push-options "--fuel 0 --ifuel 1 --query_stats"

let rec induction_props_or_hash_collision_prefix_aux
  (#vcfg:_)
  (epmax: epoch)
  (itsl: its_log vcfg {aems_equal_upto epmax itsl})
  (i: nat{let itsl_ep = prefix_within_epoch epmax itsl in
        i <= S.length itsl_ep})
  : Tot (induction_props_or_hash_collision (prefix itsl i))
    (decreases i)
  = let itsl' = prefix itsl i in
    lemma_empty_implies_induction_props itsl';
    if i = 0 then None
    else (
      let i' = i - 1 in
      let o = induction_props_or_hash_collision_prefix_aux epmax itsl i' in

      prefix_within_epoch_correct epmax itsl i';
      assert((clock itsl i').e <= epmax);

      if Some? o then o
      else
        induction_props_snoc epmax itsl i'
    )

#pop-options

let induction_props_or_hash_collision_prefix_ep
  (#vcfg:_)
  (epmax: epoch)
  (itsl: its_log vcfg {aems_equal_upto epmax itsl})
  : (let itsl_ep = prefix_within_epoch epmax itsl in
     induction_props_or_hash_collision itsl_ep)
  = let itsl_ep = prefix_within_epoch epmax itsl in
    induction_props_or_hash_collision_prefix_aux epmax itsl (S.length itsl_ep)

#push-options "--fuel 0 --ifuel 1 --query_stats"

let lemma_verifier_correct
  (#vcfg:_)
  (epmax: epoch)
  (gl: ms_verifiable_log vcfg epmax {S.length gl = vcfg.thread_count /\
                                     ~ (seq_consistent (app_fcrs_within_ep epmax gl))})
  : hash_collision vcfg.app
  = (* interleaving of gl ordered by time of each log entry *)
    let itsl = create gl in
    lemma_add_evict_set_identical_glog epmax itsl;
    assert(aems_equal_upto epmax itsl);

    (* prefix upto epoch epmax *)
    let itsl_ep = prefix_within_epoch epmax itsl in

    (* we either find a hash collision or prove itsl_ep has some nice properties *)
    let hc_or_props = induction_props_or_hash_collision_prefix_ep epmax itsl in
    if Some? hc_or_props then
      Some?.v hc_or_props
    else (
      assert(induction_props itsl_ep);

      (* this implies the the hi-level log is evict-add-consistent *)
      let itslk_ep = to_logk itsl_ep in
      assert(is_eac itslk_ep);

      (* seq of seq of app fn calls and their results which we know are not seq consistent *)
      let app_calls_ss = app_fcrs_within_ep epmax gl in
      assert(~ (seq_consistent app_calls_ss));

      lemma_fcrs_within_epoch epmax itsl;
      assert(GG.app_fcrs (to_glog itsl_ep) = app_calls_ss);

      assert(GG.app_fcrs (to_glog itsl_ep) = GG.app_fcrs (to_glog itslk_ep));
      Zeta.High.SeqConsistent.lemma_eac_implies_appfn_calls_seq_consistent itslk_ep;

      hash_collision_contra vcfg.app
    )
