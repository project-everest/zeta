module Zeta.Intermediate.Correctness

open FStar.Classical
open Zeta.BinTree
open Zeta.MultiSet
open Zeta.SeqIdx
open Zeta.App
open Zeta.AppSimulate
open Zeta.MultiSetHashDomain
open Zeta.Key
open Zeta.GenKey
open Zeta.Record
open Zeta.Time
open Zeta.HashCollision
open Zeta.Generic.Global
open Zeta.Generic.Blum
open Zeta.Intermediate.Global
open Zeta.Interleave
open Zeta.Generic.Interleave
open Zeta.Generic.Blum
open Zeta.Generic.TSLog
open Zeta.EAC
open Zeta.High.Interleave
open Zeta.High.Blum
open Zeta.High.Merkle
open Zeta.High.Verifier.EAC
open Zeta.Intermediate.VerifierConfig
open Zeta.Intermediate.Store
open Zeta.Intermediate.Verifier
open Zeta.Intermediate.StateRel
open Zeta.Intermediate.Interleave
open Zeta.Intermediate.TSLog
open Zeta.Intermediate.Blum

module S = FStar.Seq
module SA = Zeta.SeqAux
module GV = Zeta.GenericVerifier
module GG = Zeta.Generic.Global
module HI = Zeta.High.Interleave
module HV = Zeta.High.Verifier
module HM = Zeta.High.Merkle
module EAC = Zeta.EAC
module M = Zeta.Merkle
module FE = FStar.FunctionalExtensionality

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

#push-options "--fuel 0 --ifuel 1 --z3rlimit_factor 8 --query_stats"

let induction_props_implies_proving_ancestor
  (#vcfg:_)
  (il: verifiable_log vcfg)
  (i: seq_index il {let _il = prefix il i in
                    induction_props _il})
  : Lemma (ensures (let t = src il i in
                    let _vss = thread_state_pre t il i in
                    merkle_points_to_uniq _vss.st))
          [SMTPat (prefix il i)]
  = let app = vcfg.app in
    let _il = prefix il i in
    let t = src il i in
    let _vss = thread_state_pre t il i in
    let _sts = _vss.st in
    let il_ = prefix il (i+1) in
    let vss_ = thread_state_post t il i in
    let es = index il i in

    lemma_cur_thread_state_extend il i;

    let ilk = to_logk il in
    let ek = index ilk i in
    let _ilk = SA.prefix ilk i in
    let _vsk: HV.vtls_t app = thread_state_pre t ilk i in
    let _stk: HV.store_t app = _vsk.st in
    let ilk_ = SA.prefix ilk (i+1) in
    let vsk_ = thread_state_post t ilk i in

    lemma_cur_thread_state_extend ilk i;

    elim_forall_store_ismap _il t;
    assert(is_map _sts);
    elim_forall_vtls_rel _il t;
    assert(store_rel _sts _stk);

    let aux (s1 s2:_) (k:_)
      : Lemma (ensures (merkle_points_to_uniq_local _sts s1 s2 k))
              [SMTPat (merkle_points_to_uniq_local _sts s1 s2 k)]
      = if not (merkle_points_to_uniq_local _sts s1 s2 k) then (
          let mv1: M.value = to_merkle_value (stored_value _sts s1) in
          let k1:merkle_key = stored_base_key _sts s1 in
          let d1 = if M.points_to mv1 Left k then Left else Right in
          assert(M.points_to mv1 d1 k);

          let mv2: M.value = to_merkle_value (stored_value _sts s2) in
          let k2:merkle_key = stored_base_key _sts s2 in
          let d2 = if M.points_to mv2 Left k then Left else Right in
          assert(M.points_to mv2 d2 k);

          elim_is_map2 _sts s1 s2;
          assert(k1 <> k2);

          store_rel_slot _sts _stk s1;
          store_rel_slot _sts _stk s2;

          assert(HV.store_contains _stk k1);
          assert(HV.store_contains _stk k2);
          assert(HV.stored_value _stk k1 = stored_value _sts s1);
          assert(HV.stored_value _stk k2 = stored_value _sts s2);
          eac_value_is_stored_value_int _ilk k1 t;
          eac_value_is_stored_value_int _ilk k2 t;
          lemma_points_to_implies_proving_ancestor _ilk k k1 d1;
          lemma_points_to_implies_proving_ancestor _ilk k k2 d2;
          ()
        )
    in
    ()

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

let pre_store_is_map
  (#vcfg:_)
  (il: verifiable_log vcfg)
  (i: seq_index il {let _il = prefix il i in
                    induction_props _il})
  : Lemma (ensures (let t = src il i in
                    let _vss = thread_state_pre t il i in
                    is_map _vss.st))
          [SMTPat (prefix il i)]
  = let _il = prefix il i in
    let t = src il i in
    elim_forall_store_ismap _il t

let pre_vtls_rel
  (#vcfg:_)
  (il: verifiable_log vcfg)
  (i: seq_index il {let _il = prefix il i in
                    induction_props _il})
  : Lemma (ensures (let t = src il i in
                    let _vss = thread_state_pre t il i in
                    let _il = prefix il i in
                    let ilk = to_logk il in
                    let _ilk = SA.prefix ilk i in
                    let _vsk = thread_state_pre t ilk i in
                    vtls_rel _vss _vsk))
          [SMTPat (prefix il i)]
  = let _il = prefix il i in
    let t = src il i in
    elim_forall_vtls_rel _il t

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
    lemma_verifyepoch_simulates_spec _vss _vsk;
    forall_vtls_rel_snoc il_;
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

    lemma_nextepoch_simulates_spec _vss _vsk;
    forall_vtls_rel_snoc il_;

    lemma_nextepoch_preserves_ismap _vss;
    lemma_forall_store_ismap_snoc il_;

    if is_eac ilk_ then
      None
    else (
      lemma_eac_boundary_inv ilk_ i;
      Some (lemma_neac_implies_hash_collision_simple ilk_)
    )

#pop-options

let proving_ancestor (#vcfg:_)
  (il: verifiable_log vcfg)
  (i: seq_index il)
  (s: slot_id vcfg {let _il = prefix il i in
                    let t = src il i in
                    let _vss = thread_state_pre t il i in
                    let _sts = _vss.st in
                    induction_props _il /\
                    inuse_slot _sts s /\ stored_base_key _sts s <> Root})
  : merkle_key
  = let _il = prefix il i in
    let t = src il i in
    let _vss = thread_state_pre t il i in
    let _sts = _vss.st in
    let k = stored_base_key _sts s in
    let ilk = to_logk il in
    let _ilk = SA.prefix ilk i in
    HM.proving_ancestor _ilk k

#push-options "--fuel 0 --ifuel 1 --query_stats"

#push-options "--z3rlimit_factor 3"

let induction_props_implies_merkle_points_to_desc #vcfg
  (il: verifiable_log vcfg)
  (i: seq_index il {let _il = prefix il i in
                    induction_props _il})
  : Lemma (ensures (let t = src il i in
                    let _vss = thread_state_pre t il i in
                    merkle_points_to_desc _vss.st))
          [SMTPat (prefix il i)]
  = let _il = prefix il i in
    let t = src il i in
    let _vss = thread_state_pre t il i in
    let _sts = _vss.st in
    let il_ = prefix il (i+1) in
    let vss_ = thread_state_post t il i in
    let es = index il i in

    lemma_cur_thread_state_extend il i;

    let ilk = to_logk il in
    let ek = index ilk i in
    let _ilk = SA.prefix ilk i in
    let _vsk: HV.vtls_t vcfg.app = thread_state_pre t ilk i in
    let _stk = _vsk.st in
    let ilk_ = SA.prefix ilk (i+1) in
    let vsk_ = thread_state_post t ilk i in

    lemma_cur_thread_state_extend ilk i;

    let aux (s:_) (d:_)
      : Lemma (ensures (merkle_points_to_desc_local _sts s d))
              [SMTPat (merkle_points_to_desc_local _sts s d)]
      = if not (merkle_points_to_desc_local _sts s d) then (
          let mv1 = to_merkle_value (stored_value _sts s) in
          let k = stored_base_key _sts s in
          let kd = M.pointed_key mv1 d in
          assert(HV.store_contains _stk k);
          assert(HV.stored_value _stk k = stored_value _sts s);
          eac_value_is_stored_value_int _ilk k t;
          lemma_mv_points_to_dir_correct _ilk k d;
          ()
        )
    in
    ()

#pop-options

#pop-options


#push-options "--fuel 0 --ifuel 1 --query_stats"
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

    lemma_evictbm_simulates_spec _vss _vsk es;
    forall_vtls_rel_snoc il_;
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

    lemma_evictb_simulates_spec _vss _vsk es;
    forall_vtls_rel_snoc il_;

    lemma_evictb_preserves_ismap _vss es;
    lemma_forall_store_ismap_snoc il_;

    if is_eac ilk_ then
      None
    else (
      lemma_eac_boundary_inv ilk_ i;
      Some (lemma_neac_implies_hash_collision_simple ilk_)
    )

let induction_props_snoc_evictm
  (#vcfg:_)
  (il: verifiable_log vcfg)
  (i: seq_index il {let il' = prefix il i in
                    let es = index il i in
                    induction_props il' /\
                    GV.EvictM? es})
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

    lemma_evictm_simulates_spec _vss _vsk es;
    forall_vtls_rel_snoc il_;
    lemma_evictm_preserves_ismap _vss es;
    lemma_forall_store_ismap_snoc il_;

    if is_eac ilk_ then
      None
    else (
      lemma_eac_boundary_inv ilk_ i;
      Some (lemma_neac_implies_hash_collision_simple ilk_)
    )

let induction_props_snoc_runapp
  (#vcfg:_)
  (il: verifiable_log vcfg)
  (i: seq_index il {let il' = prefix il i in
                    let es = index il i in
                    induction_props il' /\
                    GV.RunApp? es})
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
    lemma_runapp_simulates_spec _vss _vsk es;
    forall_vtls_rel_snoc il_;
    lemma_runapp_preserves_ismap _vss es;
    lemma_forall_store_ismap_snoc il_;

    if is_eac ilk_ then
      None
    else (
      lemma_eac_boundary_inv ilk_ i;
      Some (lemma_neac_implies_hash_collision_simple ilk_)
    )

#pop-options
#pop-options

let addb_caseB (#vcfg:_)
  (il: verifiable_log vcfg)
  (i: seq_index il {let _il = prefix il i in
                    let es = index il i in
                    induction_props _il /\
                    GV.AddB? es})
  = let _il = prefix il i in
    let t = src il i in
    let _vss = thread_state_pre t il i in
    let GV.AddB (gk,_) _ _ _ = index il i in
    let k = to_base_key gk in
    store_contains_key _vss.st k

let addb_caseA (#vcfg:_)
  (il: verifiable_log vcfg)
  (i: seq_index il {let _il = prefix il i in
                    let es = index il i in
                    induction_props _il /\
                    GV.AddB? es})
  = not (addb_caseB il i)

#push-options "--fuel 0 --ifuel 1 --query_stats"

let addb_case_neac (#vcfg:_)
  (il: verifiable_log vcfg)
  (i: seq_index il)
  = let _il = prefix il i in
    let il_ = prefix il (i+1) in
    let es = index il i in
    induction_props _il /\
    spec_rel il_ /\
    GV.AddB? es /\
    (let ilk = to_logk il in
     let ilk_ = SA.prefix ilk (i+1) in
     let _ilk = SA.prefix ilk i in
     is_eac _ilk /\ not (is_eac ilk_))

let addb_case_neac_key (#vcfg:_)
  (il: verifiable_log vcfg)
  (i: seq_index il {addb_case_neac il i})
  = let ilk = to_logk il in
    let _ilk = SA.prefix ilk i in
    let gk,_ = GV.add_record (index il i) in
    to_base_key gk

let addb_case_neac_eacstate (#vcfg:_)
  (il: verifiable_log vcfg)
  (i: seq_index il {addb_case_neac il i})
  : EAC.eac_state vcfg.app (addb_case_neac_key il i)
  = let ilk = to_logk il in
    let _ilk = SA.prefix ilk i in
    let gk,_ = GV.add_record (index il i) in
    let k = to_base_key gk in
    HI.eac_state_of_key k _ilk

#push-options "--z3rlimit_factor 3"

let induction_props_snoc_addb_neac_eacinit
  (#vcfg:_)
  (epmax: epoch)
  (il: its_log vcfg{aems_equal_upto epmax il})
  (i: seq_index il {addb_case_neac il i /\
                    (clock il i).e <= epmax /\
                    EACInit? (addb_case_neac_eacstate il i)})
  : induction_props_or_hash_collision (prefix il (i+1))
  = let _il = prefix il i in
    let t = src il i in
    let _vss = thread_state_pre t il i in
    let il_ = prefix il (i+1) in
    let vss_ = thread_state_post t il i in
    let es = index il i in
    let GV.AddB (gk,gv) s ts td = es in
    let k = to_base_key gk in

    let ilk = to_logk il in
    let ek = index ilk i in
    let _ilk = SA.prefix ilk i in
    let _vsk = thread_state_pre t ilk i in
    let ilk_ = SA.prefix ilk (i+1) in
    let vsk_ = thread_state_post t ilk i in
    let ee = mk_vlog_entry_ext ilk_ i in

    lemma_cur_thread_state_extend il i;
    lemma_cur_thread_state_extend ilk i;

    let be = blum_add_elem il i in
    let ep = be.t.e in
    assert(ep <= epmax);

    if evict_set ep il `contains` be then (

      (* the index of the evict element should be before i *)
      let j = evict_elem_idx il be in
      lemma_evict_before_add il i;
      assert(j < i);

      assert(index il j = index _il j);
      assert(be = blum_evict_elem _il j);

      lemma_spec_rel_implies_same_evict_elem _il j;
      assert(be = blum_evict_elem _ilk j);

      assert(eac_state_of_key k _ilk = EACInit);
      eac_state_init_implies_no_key_refs k _ilk;
      assert(~ (has_some_ref_to_key k _ilk));

      assert(HV.refs_key (index _ilk j) k);
      exists_intro (fun i -> HV.refs_key (index _ilk i) k) j;
      Some (hash_collision_contra vcfg.app)
    )
    else (
      not_eq (add_set ep il) (evict_set ep il) be;
      Some (hash_collision_contra vcfg.app)
    )

#pop-options

#push-options "--z3rlimit_factor 3"

let induction_props_snoc_addb_neac_eacinstore
  (#vcfg:_)
  (epmax: epoch)
  (il: its_log vcfg {aems_equal_upto epmax il})
  (i: seq_index il {addb_case_neac il i /\
                    (clock il i).e <= epmax /\
                    EACInStore? (addb_case_neac_eacstate il i)})
  : induction_props_or_hash_collision (prefix il (i+1))
  = let _il = prefix il i in
    let t = src il i in
    let _vss = thread_state_pre t il i in
    let il_ = prefix il (i+1) in
    let vss_ = thread_state_post t il i in
    let es = index il i in
    let GV.AddB (gk,gv) s ts td = es in
    let k = to_base_key gk in

    let ilk = to_logk il in
    let ek = index ilk i in
    let _ilk = SA.prefix ilk i in
    let _vsk = thread_state_pre t ilk i in
    let ilk_ = SA.prefix ilk (i+1) in
    let vsk_ = thread_state_post t ilk i in
    let ee = mk_vlog_entry_ext ilk_ i in

    lemma_cur_thread_state_extend il i;
    lemma_cur_thread_state_extend ilk i;

    let be = eac_instore_addb_diff_elem ilk_ i in
    let ep = be.t.e in
    lemma_spec_rel_implies_same_add_elem il_ i;
    assert(ep <= epmax);

    lemma_spec_rel_implies_same_add_set ep il_;
    lemma_spec_rel_implies_same_evict_set ep il_;
    assert(mem be (add_set ep il_) > mem be (evict_set ep il_));
    lemma_evict_before_add2 ep il (i+1) be;
    assert(mem be (add_set ep il) > mem be (evict_set ep il));
    not_eq (add_set ep il) (evict_set ep il) be;
    Some (hash_collision_contra vcfg.app)

#pop-options

#push-options "--z3rlimit_factor 3"

let induction_props_snoc_addb_neac_eacevicted_merkle
  (#vcfg:_)
  (epmax: epoch)
  (il: its_log vcfg {aems_equal_upto epmax il})
  (i: seq_index il {addb_case_neac il i /\
                    (clock il i).e <= epmax /\
                    EACEvictedMerkle? (addb_case_neac_eacstate il i)})
  : induction_props_or_hash_collision (prefix il (i+1))
  = let _il = prefix il i in
    let t = src il i in
    let _vss = thread_state_pre t il i in
    let il_ = prefix il (i+1) in
    let vss_ = thread_state_post t il i in
    let es = index il i in
    let GV.AddB (gk,gv) s ts td = es in
    let k = to_base_key gk in

    let ilk = to_logk il in
    let ek = index ilk i in
    let _ilk = SA.prefix ilk i in
    let _vsk = thread_state_pre t ilk i in
    let ilk_ = SA.prefix ilk (i+1) in
    let vsk_ = thread_state_post t ilk i in
    let ee = mk_vlog_entry_ext ilk_ i in

    lemma_cur_thread_state_extend il i;
    lemma_cur_thread_state_extend ilk i;

    let be = eac_evictedm_addb_diff_elem ilk_ i in
    let ep = be.t.e in
    lemma_spec_rel_implies_same_add_elem il_ i;
    assert(ep <= epmax);

    lemma_spec_rel_implies_same_add_set ep il_;
    lemma_spec_rel_implies_same_evict_set ep il_;
    assert(mem be (add_set ep il_) > mem be (evict_set ep il_));
    lemma_evict_before_add2 ep il (i+1) be;
    assert(mem be (add_set ep il) > mem be (evict_set ep il));
    not_eq (add_set ep il) (evict_set ep il) be;
    Some (hash_collision_contra vcfg.app)

#pop-options

let induction_props_snoc_addb_neac_eacevicted_blum
  (#vcfg:_)
  (epmax: epoch)
  (il: its_log vcfg {aems_equal_upto epmax il})
  (i: seq_index il {addb_case_neac il i /\
                    (clock il i).e <= epmax /\
                    EACEvictedBlum? (addb_case_neac_eacstate il i)})
  : induction_props_or_hash_collision (prefix il (i+1))
  = let _il = prefix il i in
    let t = src il i in
    let _vss = thread_state_pre t il i in
    let il_ = prefix il (i+1) in
    let vss_ = thread_state_post t il i in
    let es = index il i in
    let GV.AddB (gk,gv) s ts td = es in
    let k = to_base_key gk in

    let ilk = to_logk il in
    let ek = index ilk i in
    let _ilk = SA.prefix ilk i in
    let _vsk = thread_state_pre t ilk i in
    let ilk_ = SA.prefix ilk (i+1) in
    let vsk_ = thread_state_post t ilk i in
    let ee = mk_vlog_entry_ext ilk_ i in

    lemma_cur_thread_state_extend il i;
    lemma_cur_thread_state_extend ilk i;

    lemma_eac_boundary_inv ilk_ i;
    assert(i = eac_boundary ilk_);
    let be = eac_evictedb_addb_diff_elem ilk_  in
    let ep = be.t.e in
    lemma_spec_rel_implies_same_add_elem il_ i;
    assert(ep <= epmax);

    lemma_spec_rel_implies_same_add_set ep il_;
    lemma_spec_rel_implies_same_evict_set ep il_;
    assert(mem be (add_set ep il_) > mem be (evict_set ep il_));
    lemma_evict_before_add2 ep il (i+1) be;
    assert(mem be (add_set ep il) > mem be (evict_set ep il));
    not_eq (add_set ep il) (evict_set ep il) be;
    Some (hash_collision_contra vcfg.app)

let induction_props_snoc_addb_neac
  (#vcfg:_)
  (epmax: epoch)
  (il: its_log vcfg {aems_equal_upto epmax il})
  (i: seq_index il {addb_case_neac il i /\
                    (clock il i).e <= epmax})
  : induction_props_or_hash_collision (prefix il (i+1))
  = match addb_case_neac_eacstate il i with
    | EACInit -> induction_props_snoc_addb_neac_eacinit epmax il i
    | EACInStore _ _ _ -> induction_props_snoc_addb_neac_eacinstore epmax il i
    | EACEvictedMerkle _ _ -> induction_props_snoc_addb_neac_eacevicted_merkle epmax il i
    | EACEvictedBlum _ _ _ _ -> induction_props_snoc_addb_neac_eacevicted_blum epmax il i

#push-options "--z3rlimit_factor 3"

let induction_props_snoc_addb_caseA
  (#vcfg:_)
  (epmax: epoch)
  (il: its_log vcfg {aems_equal_upto epmax il})
  (i: seq_index il {let il' = prefix il i in
                    let es = index il i in
                    induction_props il' /\
                    (clock il i).e <= epmax /\
                    GV.AddB? es /\
                    addb_caseA il i})
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
    lemma_vaddb_preserves_spec_new_key _vss _vsk es;
    forall_vtls_rel_snoc il_;
    lemma_vaddb_preserves_ismap_new_key _vss es;
    lemma_forall_store_ismap_snoc il_;
    if is_eac ilk_ then None
    else
      induction_props_snoc_addb_neac epmax il i

let induction_props_snoc_addb_caseB
  (#vcfg:_)
  (epmax: epoch)
  (il: its_log vcfg {aems_equal_upto epmax il})
  (i: seq_index il {let il' = prefix il i in
                    let es = index il i in
                    induction_props il' /\
                    (clock il i).e <= epmax /\
                    GV.AddB? es /\
                    addb_caseB il i})
  : induction_props_or_hash_collision (prefix il (i+1))
  = let _il = prefix il i in
    let tid = src il i in
    let _vss = thread_state_pre tid il i in
    let _sts = _vss.st in
    let il_ = prefix il (i+1) in
    let vss_ = thread_state_post tid il i in
    let es = index il i in

    lemma_cur_thread_state_extend il i;

    let ilk = to_logk il in
    let ek = index ilk i in
    let _ilk = SA.prefix ilk i in
    let _vsk: HV.vtls_t vcfg.app = thread_state_pre tid ilk i in
    let _stk = _vsk.st in
    let ilk_ = SA.prefix ilk (i+1) in
    let vsk_ = thread_state_post tid ilk i in

    lemma_cur_thread_state_extend ilk i;

    let GV.AddB (gk,gv) s t j = es in
    let k = to_base_key gk in
    assert(store_contains_key _sts k);
    assert(HV.store_contains _stk k);
    let be = blum_add_elem il i in
    let ep = be.t.e in

    eac_add_set_mem_atleast_evict_set_mem _ilk tid be;
    assert(mem be (add_set ep _il) >= mem be (evict_set ep _il));
    add_set_snoc ep il_;
    lemma_add_incr_mem #_ #_ (add_set ep _il) be;
    assert(mem be (add_set ep _il) + 1 = mem be (add_set ep il_));
    evict_set_snoc ep il_;
    lemma_evict_before_add2 ep il (i+1) be;
    assert(mem be (add_set ep il) > mem be (evict_set ep il));
    not_eq (add_set ep il) (evict_set ep il) be;
    Some (hash_collision_contra vcfg.app)

#pop-options

let induction_props_snoc_addb
  (#vcfg:_)
  (epmax: epoch)
  (il: its_log vcfg {aems_equal_upto epmax il})
  (i: seq_index il {let il' = prefix il i in
                    let es = index il i in
                    induction_props il' /\
                    (clock il i).e <= epmax /\
                    GV.AddB? es})
  : induction_props_or_hash_collision (prefix il (i+1))
  = let _il = prefix il i in
    let t = src il i in
    let _vss = thread_state_pre t il i in
    let GV.AddB (gk,_) _ _ _ = index il i in
    let k = to_base_key gk in

    if store_contains_key _vss.st k then
      induction_props_snoc_addb_caseB epmax il i
    else
      induction_props_snoc_addb_caseA epmax il i

let addm_caseA (#vcfg)
  (il: verifiable_log vcfg)
  (i: seq_index il)
  = let _il = prefix il i in
    let es = index il i in
    induction_props _il /\
    GV.AddM? es /\
    (let t = src il i in
     let _vss = thread_state_pre t il i in
     let _sts = _vss.st in
     let GV.AddM (gk, gv) s s' = es in
     let k = to_base_key gk in
     not (store_contains_key _sts k)
    )

let induction_props_snoc_addm_caseA
  (#vcfg:_)
  (il: verifiable_log vcfg)
  (i: seq_index il {addm_caseA il i})
  : induction_props_or_hash_collision (prefix il (i+1))
  = let _il = prefix il i in
    let tid = src il i in
    let _vss = thread_state_pre tid il i in
    let _sts = _vss.st in
    let il_ = prefix il (i+1) in
    let vss_ = thread_state_post tid il i in
    let es = index il i in

    lemma_cur_thread_state_extend il i;

    let ilk = to_logk il in
    let ek = index ilk i in
    let _ilk = SA.prefix ilk i in
    let _vsk: HV.vtls_t vcfg.app = thread_state_pre tid ilk i in
    let _stk = _vsk.st in
    let ilk_ = SA.prefix ilk (i+1) in
    let vsk_ = thread_state_post tid ilk i in

    lemma_cur_thread_state_extend ilk i;
    lemma_vaddm_preserves_spec_new_key _vss _vsk es;
    forall_vtls_rel_snoc il_;
    lemma_vaddm_preserves_ismap_new_key _vss es;
    lemma_forall_store_ismap_snoc il_;

    if is_eac ilk_ then
      None
    else (
      lemma_eac_boundary_inv ilk_ i;
      Some (lemma_neac_implies_hash_collision_simple ilk_)
    )

#pop-options

let addm_props (#vcfg)
  (il: verifiable_log vcfg)
  (i: seq_index il {GV.AddM? (index il i)})
  : Lemma (requires (let _il = prefix il i in
                     let es = index il i in
                     GV.AddM? (index il i) /\
                     induction_props _il))
          (ensures (let _il = prefix il i in
                    let GV.AddM (gk,gv) s s' = index il i in
                    let k = to_base_key gk in
                    let t = src il i in
                    let _vss = thread_state_pre t il i in
                    let _sts = _vss.st in
                    inuse_slot _sts s' /\ k <> Root))
          [SMTPat (index il i)]
  = lemma_cur_thread_state_extend il i

#push-options "--fuel 0 --ifuel 1 --query_stats"

let addm_caseB (#vcfg)
  (il: verifiable_log vcfg)
  (i: seq_index il)
  = let _il = prefix il i in
    let es = index il i in
    induction_props _il /\
    GV.AddM? es /\
    (let t = src il i in
     let _vss = thread_state_pre t il i in
     let _sts = _vss.st in
     let GV.AddM (gk, gv) s s' = es in
     let k = to_base_key gk in
     let k' = stored_base_key _sts s' in
     store_contains_key _sts k /\
     (let sk = slot_of_key _sts k in
      let pk = proving_ancestor il i sk in
      pk <> k'))

#push-options "--z3rlimit_factor 3"

let induction_props_snoc_addm_caseB
  (#vcfg:_)
  (il: verifiable_log vcfg)
  (i: seq_index il {addm_caseB il i})
  : induction_props_or_hash_collision (prefix il (i+1))
  = let _il = prefix il i in
    let tid = src il i in
    let _vss = thread_state_pre tid il i in
    let _sts = _vss.st in
    let il_ = prefix il (i+1) in
    let vss_ = thread_state_post tid il i in
    let es = index il i in

    lemma_cur_thread_state_extend il i;
    lemma_addm_props _vss es;

    let ilk = to_logk il in
    let ek = index ilk i in
    let _ilk = SA.prefix ilk i in
    let _vsk: HV.vtls_t vcfg.app = thread_state_pre tid ilk i in
    let _stk = _vsk.st in
    let ilk_ = SA.prefix ilk (i+1) in
    let vsk_ = thread_state_post tid ilk i in

    lemma_cur_thread_state_extend ilk i;
    let GV.AddM (gk,gv) s s' = es in
    let k' = stored_base_key _sts s' in
    let k = to_base_key gk in
    let sk = slot_of_key _sts k in
    let pk = proving_ancestor il i sk in
    let v' = to_merkle_value (stored_value _sts s') in
    let d = desc_dir k k' in

    assert(HV.store_contains _stk k');
    let aux ()
      : Lemma (ensures (k' = Root \/ not (EACInit? (eac_state_of_key k' _ilk))))
      = if k' <> Root then (
          exists_intro (fun t -> HV.store_contains (HI.thread_store t _ilk) k') tid;
          lemma_instore k' _ilk
        )
    in
    aux();
    assert(k' = Root \/ not (EACInit? (eac_state_of_key k' _ilk)));
    lemma_init_ancestor_ancestor_of_proving _ilk k k';
    eac_value_is_stored_value _ilk (IntK k') tid;

    let k2 = M.pointed_key v' d in
    lemma_proper_desc_depth_monotonic k pk;
    assert(is_desc k2 k);
    lemma_desc_depth_monotonic k2 k;
    assert(is_desc pk k2);
    lemma_desc_depth_monotonic pk k2;
    Some (hash_collision_contra vcfg.app)

#pop-options

let addm_caseC (#vcfg)
  (il: verifiable_log vcfg)
  (i: seq_index il)
  = let _il = prefix il i in
    let es = index il i in
    induction_props _il /\
    GV.AddM? es /\
    (let t = src il i in
     let _vss = thread_state_pre t il i in
     let _sts = _vss.st in
     let GV.AddM (gk, gv) s s' = es in
     let k = to_base_key gk in
     let k' = stored_base_key _sts s' in
     store_contains_key _sts k /\
     (let sk = slot_of_key _sts k in
      let pk = proving_ancestor il i sk in
      pk = k' /\
      add_method_of _sts sk = HV.MAdd))

#pop-options

#push-options "--z3rlimit_factor 3"

let induction_props_snoc_addm_caseC
  (#vcfg:_)
  (il: verifiable_log vcfg)
  (i: seq_index il {addm_caseC il i})
  : induction_props_or_hash_collision (prefix il (i+1))
  = let _il = prefix il i in
    let tid = src il i in
    let _vss = thread_state_pre tid il i in
    let _sts = _vss.st in
    let il_ = prefix il (i+1) in
    let vss_ = thread_state_post tid il i in
    let es = index il i in

    lemma_cur_thread_state_extend il i;
    lemma_addm_props _vss es;

    let ilk = to_logk il in
    let ek = index ilk i in
    let _ilk = SA.prefix ilk i in
    let _vsk: HV.vtls_t vcfg.app = thread_state_pre tid ilk i in
    let _stk = _vsk.st in
    let ilk_ = SA.prefix ilk (i+1) in
    let vsk_ = thread_state_post tid ilk i in

    lemma_cur_thread_state_extend ilk i;
    let GV.AddM (gk,gv) s s' = es in
    let k' = stored_base_key _sts s' in
    let k = to_base_key gk in
    let d = desc_dir k k' in
    let sk = slot_of_key _sts k in
    let pk = proving_ancestor il i sk in

    let sk_anc = pointing_slot _sts sk in
    assert(inuse_slot _sts sk_anc);

    let d_anc = if points_to_dir _sts sk_anc Left sk then Left else Right in
    assert(slot_points_to_is_merkle_points_to_local _sts sk_anc sk d_anc);
    let k_anc = stored_base_key _sts sk_anc in
    eac_value_is_stored_value _ilk (IntK k_anc) tid;
    lemma_points_to_implies_proving_ancestor _ilk k k_anc d_anc;
    assert(pk = k');
    assert(k' = k_anc);
    lemma_mv_points_to_dir_correct _ilk k_anc d_anc;
    lemma_ismap_correct _sts sk_anc s';
    assert(s' = sk_anc);
    assert(d_anc = d);
    assert(points_to_dir _sts sk_anc d_anc sk);
    assert(points_to_dir _sts s' d sk);
    assert(inuse_slot _sts s' && points_to_some_slot _sts s' d);
    (* super-fragile proof: uncommenting the following results in all kinds of weird errors *)
    assert(Some? (points_to_info _sts s' d));
    //assert(points_to_info _sts s' d <> None);
    //assert(not (None? (points_to_info _sts s' d)));
    //assert(not (points_to_none _sts s' d));
    Some (hash_collision_contra vcfg.app)

#pop-options

let addm_caseD (#vcfg)
  (il: verifiable_log vcfg)
  (i: seq_index il)
  = let _il = prefix il i in
    let es = index il i in
    induction_props _il /\
    GV.AddM? es /\
    (let t = src il i in
     let _vss = thread_state_pre t il i in
     let _sts = _vss.st in
     let GV.AddM (gk, gv) s s' = es in
     let k = to_base_key gk in
     let k' = stored_base_key _sts s' in
     store_contains_key _sts k /\
     (let sk = slot_of_key _sts k in
      let pk = proving_ancestor il i sk in
      pk = k' /\
      add_method_of _sts sk = HV.BAdd))

#push-options "--fuel 1 --ifuel 1 --z3rlimit_factor 3 --query_stats"

let induction_props_snoc_addm_caseD
  (#vcfg:_)
  (il: verifiable_log vcfg)
  (i: seq_index il {addm_caseD il i})
  : induction_props_or_hash_collision (prefix il (i+1))
  = let _il = prefix il i in
    let tid = src il i in
    let _vss = thread_state_pre tid il i in
    let _sts = _vss.st in
    let il_ = prefix il (i+1) in
    let vss_ = thread_state_post tid il i in
    let es = index il i in

    lemma_cur_thread_state_extend il i;
    lemma_addm_props _vss es;

    let ilk = to_logk il in
    let ek = index ilk i in
    let _ilk = SA.prefix ilk i in
    let _vsk: HV.vtls_t vcfg.app = thread_state_pre tid ilk i in
    let _stk = _vsk.st in
    let ilk_ = SA.prefix ilk (i+1) in
    let vsk_ = thread_state_post tid ilk i in

    lemma_cur_thread_state_extend ilk i;
    let GV.AddM (gk,gv) s s' = es in
    let k' = stored_base_key _sts s' in
    let k = to_base_key gk in
    let v' = to_merkle_value (stored_value _sts s') in
    let d = desc_dir k k' in
    let sk = slot_of_key _sts k in

    assert(is_map _sts);
    let _stk2 = as_map _sts in
    assert(FE.feq _stk2 _stk);
    assert(HV.store_contains _stk k);
    assert(add_method_of _sts sk = HV.BAdd);
    assert(HV.add_method_of _stk k = HV.BAdd);
    exists_intro (fun t -> HV.store_contains (HI.thread_store t _ilk) k) tid;
    lemma_instore k _ilk;
    assert(EACInStore? (eac_state_of_key k _ilk));
    key_in_unique_store k _ilk tid (stored_tid k _ilk);
    assert(tid = stored_tid k _ilk);
    eac_add_method_is_stored_addm _ilk k;
    assert(EACInStore?.m (eac_state_of_key k _ilk) = HV.BAdd);
    lemma_proving_ancestor_blum_bit _ilk k;
    eac_value_is_stored_value_int _ilk k' tid;
    assert(False);
    Some (hash_collision_contra vcfg.app)


#pop-options

#push-options "--fuel 0 --ifuel 1 --query_stats"

let induction_props_snoc_addm
  (#vcfg:_)
  (il: its_log vcfg)
  (i: seq_index il {let il' = prefix il i in
                    let es = index il i in
                    induction_props il' /\
                    GV.AddM? es})
  : induction_props_or_hash_collision (prefix il (i+1))
  = let _il = prefix il i in
    let tid = src il i in
    let _vss = thread_state_pre tid il i in
    let _sts = _vss.st in
    let il_ = prefix il (i+1) in
    let vss_ = thread_state_post tid il i in
    let es = index il i in

    lemma_cur_thread_state_extend il i;

    let ilk = to_logk il in
    let ek = index ilk i in
    let _ilk = SA.prefix ilk i in
    let _vsk: HV.vtls_t vcfg.app = thread_state_pre tid ilk i in
    let _stk = _vsk.st in
    let ilk_ = SA.prefix ilk (i+1) in
    let vsk_ = thread_state_post tid ilk i in

    lemma_cur_thread_state_extend ilk i;
    let GV.AddM (gk,gv) s s' = es in
    let k' = stored_base_key _sts s' in
    let k = to_base_key gk in

    if store_contains_key _sts k then
      let sk = slot_of_key _sts k in
      let pk = proving_ancestor il i sk in
      if pk <> k' then
        induction_props_snoc_addm_caseB il i
      else if add_method_of _sts sk = HV.MAdd then
        induction_props_snoc_addm_caseC il i
      else
        induction_props_snoc_addm_caseD il i
    else
      induction_props_snoc_addm_caseA il i

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
    | EvictM _ _ -> induction_props_snoc_evictm il i
    | RunApp _ _ _ -> induction_props_snoc_runapp il i
    | AddB _ _ _ _ -> induction_props_snoc_addb epmax il i
    | AddM _ _ _ -> induction_props_snoc_addm il i

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
