module Zeta.Intermediate.StateRel

open FStar.Classical
open Zeta.BinTree
open Zeta.Key
open Zeta.GenKey
open Zeta.Record
open Zeta.HashFunction

let empty_store_rel
  (vcfg: verifier_config)
  : Lemma (ensures (empty_store vcfg `store_rel` HV.empty_store vcfg.app))
  = let sts = empty_store vcfg in
    let stk = HV.empty_store vcfg.app in

    assert(is_map sts);
    let aux (k:_)
      : Lemma (ensures ((store_contains_key sts k = HV.store_contains stk k) /\
                       (store_contains_key sts k ==>
                       (let s = slot_of_key sts k in
                       stored_key sts s = HV.stored_key stk k /\
                       stored_value sts s = HV.stored_value stk k /\
                       add_method_of sts s = HV.add_method_of stk k))))
      = lemma_empty_contains_nokey #vcfg k;
        assert(not (store_contains_key sts k));
        assert(not (HV.store_contains stk k));
        ()
    in
    forall_intro aux

let lemma_empty_vtls_rel
  (#vcfg: verifier_config)
  (t:nat{t < vcfg.thread_count})
  : Lemma (ensures (let vss = init_thread_state vcfg t in
                    let vsk = HV.init_thread_state vcfg.app t in
                    vtls_rel vss vsk))
  = let vss = init_thread_state vcfg t in
    let sts = vss.st in
    let _sts = empty_store vcfg in
    let vsk = HV.init_thread_state vcfg.app t in
    let _stk = HV.empty_store vcfg.app in
    let stk = vsk.st in
    assert(vss.valid = vsk.valid /\ vss.tid = vsk.tid /\ vss.clock = vsk.clock);
    empty_store_rel vcfg;
    if t = 0 then
      let aux (k:_)
        : Lemma (ensures ((store_contains_key sts k = HV.store_contains stk k) /\
                         (store_contains_key sts k ==>
                         (let s = slot_of_key sts k in
                         stored_key sts s = HV.stored_key stk k /\
                         stored_value sts s = HV.stored_value stk k /\
                         add_method_of sts s = HV.add_method_of stk k))))
        = ()
      in
      forall_intro aux

let lemma_runapp_simulates_spec
      (#vcfg:_)
      (vss:vtls_t vcfg{vss.valid})
      (vsk:_ {vtls_rel vss vsk})
      (e:logS_entry vcfg{GV.is_appfn e})
  : Lemma (requires (valid_logS_entry vss e))
          (ensures (let ek = to_logk_entry vss e in
                    vtls_rel (GV.verify_step e vss) (GV.verify_step ek vsk)))
  = admit()


let amp (#vcfg:_) (vss:vtls_t vcfg {vss.valid}) (e: logS_entry vcfg {GV.AddM? e})
  : addm_param vcfg
  = let GV.AddM r s s' = e in
    AMP s r s' vss

#push-options "--fuel 0 --ifuel 1 --query_stats"

let lemma_vaddm_preserves_spec_unrelatedkey
  (#vcfg: verifier_config)
  (vss: vtls_t vcfg {vss.valid})
  (vsk: HV.vtls_t vcfg.app)
  (e: logS_entry _ {GV.AddM? e})
  (ki: base_key)
  : Lemma (requires (let sts = vss.st in
                     let a = amp vss e in
                     addm_precond a /\
                     vtls_rel vss vsk /\
                     valid_logS_entry vss e /\
                     not (store_contains_key sts (addm_base_key a)) /\
                     ki <> addm_base_key a /\
                     ki <> addm_anc_key a))
          (ensures (let ek = to_logk_entry vss e in
                    let vss_ = GV.verify_step e vss in
                    let sts_ = vss_.st in
                    let vsk_: HV.vtls_t vcfg.app = GV.verify_step ek vsk in
                    let stk_ = vsk_.st in
                    is_map sts_ /\
                    store_rel_key sts_ stk_ ki))
  = let sts = vss.st in
    let a = amp vss e in
    let stk = vsk.st in
    let ek = to_logk_entry vss e in
    let a = amp vss e in
    let GV.AddM r s s' = e in

    let k' = addm_anc_key a in
    let k = addm_base_key a in

    assert(GV.add_record ek = r);
    assert(GV.add_slot ek = k);
    assert(GV.ancestor_slot ek = k');

    store_rel_slot sts stk s';
    assert(HV.store_contains stk k');
    assert(HV.stored_value stk k' = stored_value sts s');

    let d = addm_dir a in
    let vss_ = GV.verify_step e vss in
    let sts_ = vss_.st in
    let vsk_: HV.vtls_t vcfg.app = GV.verify_step ek vsk in
    let stk_ = vsk_.st in

    lemma_vaddm_preserves_ismap_new_key vss e;
    assert(is_map sts_);

    elim_key_store_rel sts stk ki;
    if HV.store_contains stk ki then (
      let si = slot_of_key sts ki in

      (* si cannot be s or s' since the key stored there is ki *)
      assert(stored_base_key sts si = ki);
      assert(si <> s /\ si <> s');

      lemma_addm_identical_except2 vss e si
    )

let lemma_vaddm_preserves_spec_key
  (#vcfg: verifier_config)
  (vss: vtls_t vcfg {vss.valid})
  (vsk: HV.vtls_t vcfg.app)
  (e: logS_entry _ {GV.AddM? e})
  : Lemma (requires (let sts = vss.st in
                     let a = amp vss e in
                     addm_precond a /\
                     vtls_rel vss vsk /\
                     valid_logS_entry vss e /\
                     not (store_contains_key sts (addm_base_key a))))
          (ensures (let ek = to_logk_entry vss e in
                    let vss_ = GV.verify_step e vss in
                    let sts_ = vss_.st in
                    let vsk_: HV.vtls_t vcfg.app = GV.verify_step ek vsk in
                    let stk_ = vsk_.st in
                    let a = amp vss e in
                    let k = addm_base_key a in
                    is_map sts_ /\
                    store_rel_key sts_ stk_ k))
  = lemma_vaddm_preserves_ismap_new_key vss e

let lemma_vaddm_preserves_spec_anc_key
  (#vcfg: verifier_config)
  (vss: vtls_t vcfg {vss.valid})
  (vsk: HV.vtls_t vcfg.app)
  (e: logS_entry _ {GV.AddM? e})
  : Lemma (requires (let sts = vss.st in
                     let a = amp vss e in
                     addm_precond a /\
                     vtls_rel vss vsk /\
                     valid_logS_entry vss e /\
                     not (store_contains_key sts (addm_base_key a))))
          (ensures (let ek = to_logk_entry vss e in
                    let vss_ = GV.verify_step e vss in
                    let sts_ = vss_.st in
                    let vsk_: HV.vtls_t vcfg.app = GV.verify_step ek vsk in
                    let stk_ = vsk_.st in
                    let a = amp vss e in
                    let k = addm_anc_key a in
                    is_map sts_ /\
                    store_rel_key sts_ stk_ k))
  = lemma_vaddm_preserves_ismap_new_key vss e

let lemma_vaddm_preserves_spec_case_valid
  (#vcfg: verifier_config)
  (vss: vtls_t vcfg {vss.valid})
  (vsk: HV.vtls_t vcfg.app)
  (e: logS_entry _ {GV.AddM? e})
  : Lemma (requires (let sts = vss.st in
                     let a = amp vss e in
                     addm_precond a /\
                     vtls_rel vss vsk /\
                     valid_logS_entry vss e /\
                     not (store_contains_key sts (addm_base_key a))))
          (ensures (let ek = to_logk_entry vss e in
                    let vss_ = GV.verify_step e vss in
                    let vsk_: HV.vtls_t vcfg.app = GV.verify_step ek vsk in
                    vtls_rel vss_ vsk_))
  = let sts = vss.st in
    let a = amp vss e in
    let stk = vsk.st in
    let ek = to_logk_entry vss e in
    let a = amp vss e in
    let GV.AddM r s s' = e in

    let k' = addm_anc_key a in
    let k = addm_base_key a in

    assert(GV.add_record ek = r);
    assert(GV.add_slot ek = k);
    assert(GV.ancestor_slot ek = k');

    store_rel_slot sts stk s';
    assert(HV.store_contains stk k');
    assert(HV.stored_value stk k' = stored_value sts s');

    let d = addm_dir a in
    let vss_ = GV.verify_step e vss in
    let sts_ = vss_.st in
    let vsk_: HV.vtls_t vcfg.app = GV.verify_step ek vsk in
    let stk_ = vsk_.st in

    lemma_vaddm_preserves_ismap_new_key vss e;
    assert(is_map sts_);

    assert(vss_.valid = vsk_.valid);
    assert(vss_.clock = vsk_.clock);
    assert(vss_.tid = vsk_.tid);

    let aux (k2:_)
      : Lemma (ensures (store_rel_key sts_ stk_ k2))
      = if k2 = k then lemma_vaddm_preserves_spec_key vss vsk e
        else if k2 = k' then lemma_vaddm_preserves_spec_anc_key vss vsk e
        else lemma_vaddm_preserves_spec_unrelatedkey vss vsk e k2
    in
    forall_intro aux;
    assert(store_rel sts_ stk_);
    ()

let lemma_vaddm_preserves_spec_case_fail
  (#vcfg: verifier_config)
  (vss: vtls_t vcfg {vss.valid})
  (vsk: HV.vtls_t vcfg.app)
  (e: logS_entry _ {GV.AddM? e})
  : Lemma (requires (let sts = vss.st in
                     let a = amp vss e in
                     ~ (addm_precond a) /\
                     vtls_rel vss vsk /\
                     valid_logS_entry vss e /\
                     not (store_contains_key sts (addm_base_key a)) /\
                     slot_points_to_is_merkle_points_to sts))
          (ensures (let ek = to_logk_entry vss e in
                    let vss_ = GV.verify_step e vss in
                    let vsk_: HV.vtls_t vcfg.app = GV.verify_step ek vsk in
                    vtls_rel vss_ vsk_))
  = let sts = vss.st in
    let a = amp vss e in
    let stk = vsk.st in
    let ek = to_logk_entry vss e in
    let a = amp vss e in
    let GV.AddM r s s' = e in

    (* otherwise e would not be a valid log entry *)
    assert(empty_slot sts s /\ inuse_slot sts s');

    let k = addm_base_key a in
    let k' = stored_base_key sts s' in

    elim_key_store_rel sts stk k';
    lemma_ismap_correct sts s' (slot_of_key sts k');

    if is_proper_desc k k' then (
      assert(addm_precond1 a);

      (* ancestor merkle value in intermediate *)
      let mvs' = addm_anc_val_pre a in
      let d = addm_dir a in

      (* and it should be the same in spec *)
      assert(HV.stored_value stk k' = IntV mvs');

      if Merkle.points_to_none mvs' d then (

        assert(addm_precond2 a /\ addm_anc_points_null a);

        (* since a does not satisfy precond, one of these should hold *)
        assert(not (is_init_record r) \/ points_to_some_slot sts s' d);

        if is_init_record r then (
          (* intermediate fails because s' points to some slot along addm direction *)
          assert(points_to_some_slot sts s' d);

          let s2 = pointed_slot sts s' d in
          assert(slot_points_to_is_merkle_points_to_local sts s' s2 d);

          (* which produces a contradiction since we have mv_points_none mvs' d *)
          assert(False);
          ()
        )
      )
      else if Merkle.points_to mvs' d k then (
        let _,gv = r in
        assert(addm_precond2 a /\ addm_anc_points_to_key a);
        assert(Merkle.desc_hash mvs' d <> Merkle.Desc k (hashfn gv) false \/
               points_to_some_slot sts s' d);

        if Merkle.desc_hash mvs' d = Merkle.Desc k (hashfn gv) false then (
          let s2 = pointed_slot sts s' d in
          assert(slot_points_to_is_merkle_points_to_local sts s' s2 d);
          assert(stored_base_key sts s2 = k);
          (* this imnplies s2 is in fact s, which is a contradiction (since s is inuse_slot then )*)
          lemma_ismap_correct sts s s2;
          assert(s = s2);

          assert(False)
        )
      )
    )

#pop-options

let lemma_vaddm_preserves_spec_new_key
      (#vcfg:_)
      (vs:vtls_t vcfg{vs.valid})
      (vs':_ {vtls_rel vs vs'})
      (e:logS_entry _{GV.AddM? e})
  : Lemma (requires (let st = vs.st in
                     let GV.AddM (gk,gv) _  _ = e in
                     let k = to_base_key gk in
                     valid_logS_entry vs e /\
                     not (store_contains_key st k) /\
                     slot_points_to_is_merkle_points_to st))
          (ensures (let ek = to_logk_entry vs e in
                    vtls_rel (GV.verify_step e vs) (GV.verify_step ek vs')))
  = if (GV.verify_step e vs).valid then
      lemma_vaddm_preserves_spec_case_valid vs vs' e
    else
      lemma_vaddm_preserves_spec_case_fail vs vs' e

let lemma_vaddb_preserves_spec_new_key
      (#vcfg:_)
      (vs:vtls_t vcfg{vs.valid})
      (vs':_ {vtls_rel vs vs'})
      (e:logS_entry _{GV.AddB? e})
  : Lemma (requires (let st = vs.st in
                     let GV.AddB (gk,gv) _  _ _ = e in
                     let k = to_base_key gk in
                     valid_logS_entry vs e /\
                     not (store_contains_key st k)))
          (ensures (let ek = to_logk_entry vs e in
                    vtls_rel (GV.verify_step e vs) (GV.verify_step ek vs')))
  = admit()
