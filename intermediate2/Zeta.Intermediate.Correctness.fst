module Zeta.Intermediate.Correctness

open Zeta.App
open Zeta.AppSimulate
open Zeta.Time
open Zeta.HashCollision
open Zeta.Generic.Global
open Zeta.Generic.Blum
open Zeta.Intermediate.Global
open Zeta.Interleave
open Zeta.Generic.Interleave
open Zeta.Generic.TSLog
open Zeta.High.Interleave
open Zeta.High.Verifier.EAC
open Zeta.Intermediate.Store
open Zeta.Intermediate.Verifier
open Zeta.Intermediate.StateRel
open Zeta.Intermediate.Interleave
open Zeta.Intermediate.TSLog

module S = FStar.Seq
module SA = Zeta.SeqAux
module GV = Zeta.GenericVerifier
module GG = Zeta.Generic.Global
module HI = Zeta.High.Interleave

#push-options "--fuel 0 --ifuel 1 --query_stats"

let lemma_eac_boundary_inv (#app:_) (#n:pos) (il: HI.verifiable_log app n) (i: seq_index il)
  : Lemma (requires (let _il = prefix il i in
                     let il_ = prefix il (i+1) in
                     is_eac _il /\ not (is_eac il_)))
          (ensures (eac_boundary il = i))
          [SMTPat (prefix il i)]
  = let _il = prefix il i in
    let il_ = prefix il (i+1) in
    let i' = eac_boundary il in
    if i' < i then
      lemma_eac_implies_prefix_eac _il (i'+1)
    else if i < i' then
      lemma_eac_implies_prefix_eac (prefix il i') (i+1)

#pop-options

(*
 * A bunch of properties we use in the induction step:
 *    (a) the intermediate verifiers all satisfy the store invariant
 *    (b) the intermediate and spec level verifiers states correspond to one-another (related)
 *    (c) the spec level log is time sorted (b and c imply that the spec log has type its_log)
 *    (d) the spec level log is evict-add-consistent
 * TODO: rename this
 *)
#push-options "--fuel 0 --ifuel 1 --query_stats"

let induction_props #vcfg (ils: verifiable_log vcfg) =
  let ilk = to_logk ils in
  spec_rel ils /\
  is_eac ilk

#pop-options

let induction_props_or_hash_collision #vcfg (ils: verifiable_log vcfg) =
  o:option (hash_collision vcfg.app) {Some? o \/ induction_props ils}

#push-options "--fuel 0 --ifuel 1 --query_stats"

let lemma_empty_implies_induction_props #vcfg (il: verifiable_log vcfg)
  : Lemma (ensures (length il = 0 ==> induction_props il))
  = if length il = 0 then (
      lemma_empty_implies_spec_rel il;
      empty_implies_eac (to_logk il)
    )

let induction_props_snoc_verifyepoch
  (#vcfg:_)
  (il: verifiable_log vcfg)
  (i: seq_index il {let il' = prefix il i in
                    let es = index il i in
                    induction_props il' /\
                    GV.VerifyEpoch? es})
  : induction_props_or_hash_collision (prefix il (i+1))
  = let _il = prefix il i in
    let t = src il i in
    let _vss = thread_state_pre t il i in
    let il_ = prefix il (i+1) in
    let vss_ = thread_state_post t il i in
    let es = index il i in

    (* _vss and vss_ are identical since VerifyEpoch does not alter state *)
    lemma_cur_thread_state_extend il i;
    assert(vss_ == _vss);

    let ilk = to_logk il in
    let ek = index ilk i in
    let _ilk = SA.prefix ilk i in
    let _vsk = thread_state_pre t ilk i in
    let ilk_ = SA.prefix ilk (i+1) in
    let vsk_ = thread_state_post t ilk i in

    (* _vsk and vsk_ are identical since *)
    lemma_cur_thread_state_extend ilk i;

    elim_forall_vtls_rel _il t;
    lemma_verifyepoch_simulates_spec _vss _vsk;
    forall_vtls_rel_snoc il_;

    elim_forall_store_ismap _il t;
    lemma_verifyepoch_preserves_ismap _vss;
    lemma_forall_store_ismap_snoc il_;

    if is_eac ilk_ then
      None
    else (
      lemma_eac_boundary_inv ilk_ i;
      Some (lemma_neac_implies_hash_collision_simple ilk_)
    )

let induction_props_snoc_next_epoch
  (#vcfg:_)
  (il: verifiable_log vcfg)
  (i: seq_index il {let il' = prefix il i in
                    let es = index il i in
                    induction_props il' /\
                    GV.NextEpoch? es})
  : induction_props_or_hash_collision (prefix il (i+1))
  = let _il = prefix il i in
    let t = src il i in
    let _vss = thread_state_pre t il i in
    let il_ = prefix il (i+1) in
    let vss_ = thread_state_post t il i in
    let es = index il i in

    lemma_cur_thread_state_extend il i;

    let ilk = to_logk il in
    let ek = index ilk i in
    let _ilk = SA.prefix ilk i in
    let _vsk = thread_state_pre t ilk i in
    let ilk_ = SA.prefix ilk (i+1) in
    let vsk_ = thread_state_post t ilk i in

    lemma_cur_thread_state_extend ilk i;

    elim_forall_vtls_rel _il t;
    lemma_nextepoch_simulates_spec _vss _vsk;
    forall_vtls_rel_snoc il_;

    elim_forall_store_ismap _il t;
    lemma_nextepoch_preserves_ismap _vss;
    lemma_forall_store_ismap_snoc il_;

    if is_eac ilk_ then
      None
    else (
      lemma_eac_boundary_inv ilk_ i;
      Some (lemma_neac_implies_hash_collision_simple ilk_)
    )

let induction_props_implies_merkle_points_to_desc #vcfg
  (il: verifiable_log vcfg)
  (i: seq_index il {let _il = prefix il i in
                    induction_props _il})
  : Lemma (ensures (let t = src il i in
                    let _vss = thread_state_pre t il i in
                    merkle_points_to_desc _vss.st))
          [SMTPat (prefix il i)]
  = admit()

let induction_props_implies_proving_ancestor
  (#vcfg:_)
  (il: verifiable_log vcfg)
  (i: seq_index il {let _il = prefix il i in
                    induction_props _il})
  : Lemma (ensures (let t = src il i in
                    let _vss = thread_state_pre t il i in
                    merkle_points_to_uniq _vss.st))
          [SMTPat (prefix il i)]
  = admit()

#push-options "--z3rlimit_factor 3"

let induction_props_snoc_evictbm
  (#vcfg:_)
  (il: verifiable_log vcfg)
  (i: seq_index il {let il' = prefix il i in
                    let es = index il i in
                    induction_props il' /\
                    GV.EvictBM? es})
  : induction_props_or_hash_collision (prefix il (i+1))
  = let _il = prefix il i in
    let t = src il i in
    let _vss = thread_state_pre t il i in
    let il_ = prefix il (i+1) in
    let vss_ = thread_state_post t il i in
    let es = index il i in

    lemma_cur_thread_state_extend il i;

    let ilk = to_logk il in
    let ek = index ilk i in
    let _ilk = SA.prefix ilk i in
    let _vsk = thread_state_pre t ilk i in
    let ilk_ = SA.prefix ilk (i+1) in
    let vsk_ = thread_state_post t ilk i in

    lemma_cur_thread_state_extend ilk i;

    elim_forall_vtls_rel _il t;
    lemma_evictbm_simulates_spec _vss _vsk es;
    forall_vtls_rel_snoc il_;

    elim_forall_store_ismap _il t;
    lemma_evictbm_preserves_ismap _vss es;
    lemma_forall_store_ismap_snoc il_;

    if is_eac ilk_ then
      None
    else (
      lemma_eac_boundary_inv ilk_ i;
      Some (lemma_neac_implies_hash_collision_simple ilk_)
    )

let induction_props_snoc_evictb
  (#vcfg:_)
  (il: verifiable_log vcfg)
  (i: seq_index il {let il' = prefix il i in
                    let es = index il i in
                    induction_props il' /\
                    GV.EvictB? es})
  : induction_props_or_hash_collision (prefix il (i+1))
  = let _il = prefix il i in
    let t = src il i in
    let _vss = thread_state_pre t il i in
    let il_ = prefix il (i+1) in
    let vss_ = thread_state_post t il i in
    let es = index il i in

    lemma_cur_thread_state_extend il i;

    let ilk = to_logk il in
    let ek = index ilk i in
    let _ilk = SA.prefix ilk i in
    let _vsk = thread_state_pre t ilk i in
    let ilk_ = SA.prefix ilk (i+1) in
    let vsk_ = thread_state_post t ilk i in

    lemma_cur_thread_state_extend ilk i;

    elim_forall_vtls_rel _il t;
    lemma_evictb_simulates_spec _vss _vsk es;
    forall_vtls_rel_snoc il_;

    elim_forall_store_ismap _il t;
    lemma_evictb_preserves_ismap _vss es;
    lemma_forall_store_ismap_snoc il_;

    if is_eac ilk_ then
      None
    else (
      lemma_eac_boundary_inv ilk_ i;
      Some (lemma_neac_implies_hash_collision_simple ilk_)
    )
#pop-options


let induction_props_snoc
  (#vcfg:_)
  (epmax: epoch)
  (il: its_log vcfg {aems_equal_upto epmax il})
  (i: seq_index il {let il' = prefix il i in
                    (clock il i).e <= epmax /\
                    induction_props il'})
  : induction_props_or_hash_collision (prefix il (i+1))
  = let es = index il i in
    let open Zeta.GenericVerifier in
    match es with
    | VerifyEpoch -> induction_props_snoc_verifyepoch il i
    | NextEpoch -> induction_props_snoc_next_epoch il i
    | EvictBM _ _ _ -> induction_props_snoc_evictbm il i
    | EvictB _ _ -> induction_props_snoc_evictb il i
    | _ ->
  admit()


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
