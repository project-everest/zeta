module Zeta.Intermediate.StateRel

open FStar.Classical
open Zeta.BinTree
open Zeta.SeqIdx
open Zeta.App
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

(* all slots in a sequence in use *)
let all_slots_inuse (#vcfg:_) (st: vstore vcfg) (ss: S.seq (slot_id vcfg))
  = forall i. (inuse_slot st (S.index ss i))

let all_slots_inuse_comp (#vcfg:_) (st: vstore vcfg) (ss: S.seq (slot_id vcfg))
  : b:bool {b <==> all_slots_inuse st ss}
  = not (exists_elems_with_prop_comp (fun s -> empty_slot st s) ss)

noeq type appfn_rel_t (vcfg: verifier_config) =
  | AFR: vss: vtls_t vcfg {vss.valid} ->
         vsk: _ {vtls_rel vss vsk} ->
         e: logS_entry vcfg {GV.is_appfn e /\ valid_logS_entry vss e} -> appfn_rel_t vcfg

let int_state (#vcfg:_) (a: appfn_rel_t vcfg)
  = a.vss

let int_store (#vcfg:_) (a: appfn_rel_t vcfg)
  = a.vss.st

let hi_state (#vcfg:_)  (a: appfn_rel_t vcfg)
  : HV.vtls_t vcfg.app
  = a.vsk

let hi_store (#vcfg:_) (a: appfn_rel_t vcfg)
  : HV.store_t vcfg.app
  = (hi_state a).st

let int_slots (#vcfg:_) (a: appfn_rel_t vcfg)
  : ss:S.seq (slot_id vcfg) {all_slots_inuse (int_store a) ss}
  = GV.RunApp?.rs a.e

let hi_entry (#vcfg:_) (a: appfn_rel_t vcfg)
  : logK_entry vcfg.app
  = to_logk_entry a.vss a.e

let hi_slots (#vcfg:_) (a: appfn_rel_t vcfg)
  : S.seq base_key
  = GV.RunApp?.rs (hi_entry a)

let slot_key_list_rel (#vcfg:_)
  (sts: vstore vcfg)
  (stk: _ {store_rel sts stk})
  (ss: _ {all_slots_inuse sts ss})
  (ks: S.seq base_key)
  = S.length ss = S.length ks /\
    (forall i. (stored_base_key sts (S.index ss i) = S.index ks i))

let lemma_appfn_slot_key_rel (#vcfg:_) (a: appfn_rel_t vcfg)
  : Lemma (ensures (slot_key_list_rel (int_store a) (hi_store a) (int_slots a) (hi_slots a)))
  = ()

let to_hv_store (#vcfg:_) (vsk: HV.vtls_t vcfg.app)
  : HV.store_t vcfg.app
  = vsk.st

let contains_distinct_app_keys_rel_aux (#vcfg:_)
  (vss: vtls_t vcfg {vss.valid})
  (vsk: _ {vtls_rel vss vsk})
  (ss: _ {all_slots_inuse vss.st ss})
  (ks: _ {let sts = vss.st in
          let stk = to_hv_store vsk in
          slot_key_list_rel sts stk ss ks})
  : Lemma (ensures (let intspec = int_verifier_spec vcfg in
                    let hispec = HV.high_verifier_spec vcfg.app in
                    GV.contains_distinct_app_keys #intspec vss ss <==>
                    GV.contains_distinct_app_keys #hispec vsk ks))
  = ()

let contains_distinct_app_keys_rel (#vcfg:_) (a: appfn_rel_t vcfg)
  : Lemma (ensures (let intspec = int_verifier_spec vcfg in
                    let hispec = HV.high_verifier_spec vcfg.app in
                    GV.contains_distinct_app_keys #intspec (int_state a) (int_slots a) <==>
                    GV.contains_distinct_app_keys #hispec (hi_state a) (hi_slots a)))
  = let vss = int_state a in
    let vsk = hi_state a in
    let ss = int_slots a in
    let ks = hi_slots a in
    contains_distinct_app_keys_rel_aux vss vsk ss ks

let contains_distinct_app_keys (#vcfg:_) (a: appfn_rel_t vcfg)
  : bool
  = let intspec = int_verifier_spec vcfg in
    let hispec = HV.high_verifier_spec vcfg.app in
    GV.contains_distinct_app_keys_comp #intspec (int_state a) (int_slots a) &&
    GV.contains_distinct_app_keys_comp #hispec (hi_state a) (hi_slots a)

let int_reads (#vcfg:_) (a: appfn_rel_t vcfg {contains_distinct_app_keys a})
  : S.seq (app_record vcfg.app.adm)
  = let intspec = int_verifier_spec vcfg in
    GV.reads #intspec (int_state a) (int_slots a)

let hi_reads (#vcfg:_) (a: appfn_rel_t vcfg {contains_distinct_app_keys a})
  : S.seq (app_record vcfg.app.adm)
  = let hispec = HV.high_verifier_spec vcfg.app in
    GV.reads #hispec (hi_state a) (hi_slots a)

let reads_rel (#vcfg:_) (a: appfn_rel_t vcfg)
  : Lemma (requires (contains_distinct_app_keys a))
          (ensures (int_reads a == hi_reads a))
  = let intspec = int_verifier_spec vcfg in
    let hispec = HV.high_verifier_spec vcfg.app in
    let vss = int_state a in
    let ss = int_slots a in
    let rss = GV.reads #intspec vss ss in

    let vsk = hi_state a  in
    let ks = hi_slots a in
    let rsk = GV.reads #hispec vsk ks in

    assert(S.length rss = S.length rsk);
    let aux (i:_)
      : Lemma (ensures (S.index rss i == S.index rsk i))
      = ()
    in
    forall_intro aux;
    assert(S.equal rss rsk)

let int_appfn_succ (#vcfg:_) (a: appfn_rel_t vcfg)
  : bool
  = let GV.RunApp f p _ = a.e in
    let ss = int_slots a in
    contains_distinct_app_keys a &&
    S.length ss = appfn_arity f &&
    (let rs = int_reads a in
     let fn = appfn f in
     let rc,_,_ = fn p rs in
     rc = Fn_success
    )

let hi_appfn_succ (#vcfg:_) (a: appfn_rel_t vcfg)
  : bool
  = let GV.RunApp f p _ = (hi_entry a) in
    let ks = hi_slots a in
    contains_distinct_app_keys a &&
    S.length ks = appfn_arity f &&
    (let rs = hi_reads a in
     let fn = appfn f in
     let rc,_,_ = fn p rs in
     rc = Fn_success
    )

let lemma_appfn_succ_rel (#vcfg:_) (a: appfn_rel_t vcfg)
  : Lemma (ensures (int_appfn_succ a = hi_appfn_succ a))
  = if contains_distinct_app_keys a then
      let ss = int_slots a in
      let ks = hi_slots a in
      let GV.RunApp f p _ = a.e in

      if S.length ss = appfn_arity f then
        reads_rel a

let int_writes (#vcfg:_) (a: appfn_rel_t vcfg {int_appfn_succ a})
  : S.seq (app_value_nullable vcfg.app.adm)
  = let GV.RunApp f p _ = a.e in
    let ss = int_slots a in
    let rs = int_reads a in
    let fn = appfn f in
    let _,_,ws = fn p rs in
    ws


let hi_writes (#vcfg:_) (a: appfn_rel_t vcfg {hi_appfn_succ a})
  : S.seq (app_value_nullable vcfg.app.adm)
  = let GV.RunApp f p _ = a.e in
    let ss = hi_slots a in
    let rs = hi_reads a in
    let fn = appfn f in
    let _,_,ws = fn p rs in
    ws

let writes_rel (#vcfg:_) (a: appfn_rel_t vcfg {int_appfn_succ a})
  : Lemma (ensures (hi_appfn_succ a /\ int_writes a == hi_writes a))
  = lemma_appfn_succ_rel a;
    assert(hi_appfn_succ a);
    reads_rel a

#push-options "--z3rlimit_factor 3"

let lemma_runapp_simulates_spec
      (#vcfg:_)
      (vss:vtls_t vcfg{vss.valid})
      (vsk:_ {vtls_rel vss vsk})
      (e:logS_entry vcfg{GV.is_appfn e})
  : Lemma (requires (valid_logS_entry vss e))
          (ensures (let ek = to_logk_entry vss e in
                    vtls_rel (GV.verify_step e vss) (GV.verify_step ek vsk)))
  = let a = AFR vss vsk e in
    let ek = hi_entry a in
    let vss_ = GV.verify_step e vss in
    let vsk_: HV.vtls_t vcfg.app = GV.verify_step ek vsk in
    let GV.RunApp f p ss = e in

    contains_distinct_app_keys_rel a;
    if contains_distinct_app_keys a && S.length ss = appfn_arity f then (
      reads_rel a;
      lemma_appfn_succ_rel a;
      if int_appfn_succ a then (
        assert (hi_appfn_succ a);
        writes_rel a;
        let wss = int_writes a in
        let wsk = hi_writes a in
        assert (wss == wsk);
        admit()
      )
      else (
        assert (GV.contains_distinct_app_keys_comp vss ss);
        assert (S.length ss = appfn_arity f);
        let fn = appfn f in
        let rs = GV.reads vss ss in
        assert(rs == int_reads a);
        assert (not (vss_.valid));
        assert (not (vsk_.valid));
        ()
      )
    )

#pop-options

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

#push-options "--fuel 2 --ifuel 2 --z3rlimit_factor 3 --query_stats"

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
  = let vss = vs in
    let sts = vs.st in

    (* explicit cast needed to help resolve .st below *)
    let vsk: HV.vtls_t vcfg.app = vs' in
    let stk = vsk.st in
    let GV.AddB r s t j = e in
    let gk,gv = r in
    let k = to_base_key gk in
    let ek = to_logk_entry vss e in

    (* otherwise, not valid_logS_entry e *)
    assert(empty_slot sts s);

    if k <> Root then (
      let vss_ = GV.verify_step e vss in
      let sts_ = vss_.st in
      lemma_vaddb_preserves_ismap_new_key vss e;

      let vsk_: HV.vtls_t vcfg.app  = GV.verify_step ek vsk in
      let stk_ = vsk_.st in
      let aux (ki:_)
        : Lemma (ensures (store_rel_key sts_ stk_ ki))
        = if ki <> k then (
            elim_key_store_rel sts stk ki;
            if HV.store_contains stk_ ki then (
              assert(HV.store_contains stk ki);
              let si = slot_of_key sts ki in
              assert (si <> s);

              assert(get_slot sts si = get_slot sts_ si)
            )
            else (
              assert(not (HV.store_contains stk ki));
              assert(not (store_contains_key sts ki));
              if store_contains_key sts_ ki then (
                let si = slot_of_key sts_ ki in
                assert(si <> s);
                ()
              )
            )
          )
      in
      forall_intro aux
    )

let lemma_points_to_some_implies_has_instore_merkle_desc
  (#vcfg:_)
  (sts: vstore vcfg)
  (stk: HV.store_t vcfg.app)
  (s: inuse_slot_id sts)
  : Lemma (requires (store_rel sts stk /\
                     slot_points_to_is_merkle_points_to sts /\
                     merkle_points_to_uniq sts /\
                     merkle_points_to_desc sts /\
                     (points_to_some_slot sts s Left || points_to_some_slot sts s Right)))
          (ensures (let k = stored_base_key sts s in
                    HV.has_instore_merkle_desc stk k)) =
  let k = stored_base_key sts s in
  let d = if points_to_some_slot sts s Left then Left else Right in
  let sd = pointed_slot sts s d in
  assert(slot_points_to_is_merkle_points_to_local sts s sd d);
  assert(points_to_dir sts s d sd);
  assert(inuse_slot sts sd);

  let mv = to_merkle_value (stored_value sts s) in
  let kd = stored_base_key sts sd in
  assert(Merkle.points_to mv d kd);
  assert(HV.store_contains stk kd);
  assert(mv = to_merkle_value (HV.stored_value stk k));
  assert(add_method_of sts sd = HV.MAdd);
  ()

let lemma_has_instore_merkle_desc_implies_slot_points_to
  (#vcfg:_)
  (sts: vstore vcfg)
  (stk: HV.store_t vcfg.app)
  (s: inuse_slot_id sts)
  : Lemma (requires (let k = stored_base_key sts s in
                     store_rel sts stk /\
                     slot_points_to_is_merkle_points_to sts /\
                     merkle_points_to_uniq sts /\
                     merkle_points_to_desc sts /\
                     HV.store_contains stk k /\
                     HV.has_instore_merkle_desc stk k))
          (ensures (points_to_some_slot sts s Left || points_to_some_slot sts s Right )) =
  let k = stored_base_key sts s in
  assert(HV.has_instore_merkle_desc stk k);
  assert(is_merkle_key k);
  let mv = to_merkle_value (HV.stored_value stk k) in
  assert(mv = to_merkle_value (stored_value sts s));
  let ld = Merkle.desc_hash mv Left in
  let rd = Merkle.desc_hash mv Right in

  assert(Merkle.Desc? ld && HV.is_instore_madd stk (Merkle.Desc?.k ld) ||
    Merkle.Desc? rd && HV.is_instore_madd stk (Merkle.Desc?.k rd));

  let d = if Merkle.Desc? ld && HV.is_instore_madd stk (Merkle.Desc?.k ld) then Left else Right in
  let kd = Merkle.pointed_key mv d in

  assert(HV.store_contains stk kd /\ HV.add_method_of stk kd = HV.MAdd);
  let sd = slot_of_key sts kd in
  assert(stored_base_key sts sd = kd /\ add_method_of sts sd = HV.MAdd);
  assert(merkle_points_to_desc_local sts s d);

  assert(kd <> Root);
  let s2 = pointing_slot sts sd in
  assert(points_to sts s2 sd);

  let d2 = if points_to_dir sts s2 Left sd then Left else Right in
  assert(points_to_dir sts s2 d2 sd);
  assert(slot_points_to_is_merkle_points_to_local sts s2 sd d2);
  let mv2 = to_merkle_value (stored_value sts s2) in

  assert(Merkle.points_to mv2 d2 kd);
  assert(Merkle.points_to mv d kd);

  if s2 = s then ()
  else (
    assert(merkle_points_to_uniq_local sts s s2 kd);
    ()
  )

let lemma_evictb_simulates_spec
      (#vcfg:_)
      (vs:vtls_t vcfg{vs.valid})
      (vs':_ {vtls_rel vs vs'})
      (e:logS_entry vcfg{GV.EvictB? e})
  : Lemma (requires (let st = vs.st in
                     valid_logS_entry vs e /\
                     slot_points_to_is_merkle_points_to st /\
                     merkle_points_to_uniq st /\
                     merkle_points_to_desc st))
          (ensures (let ek = to_logk_entry vs e in
                    vtls_rel (GV.verify_step e vs) (GV.verify_step ek vs')))
  = let vss = vs in
    let sts = vs.st in

    (* explicit cast needed to help resolve .st below *)
    let vsk: HV.vtls_t vcfg.app = vs' in
    let stk = vsk.st in
    let GV.EvictB s t = e in
    assert(inuse_slot sts s);
    let clk = vss.clock in
    let open Zeta.Time in

    let k = stored_base_key sts s in
    let ek = to_logk_entry vss e in
    let vss_ = GV.verify_step e vss in
    let sts_ = vss_.st in
    let vsk_: HV.vtls_t vcfg.app = GV.verify_step ek vsk in
    if k <> Root && clk `ts_lt` t then
      if points_to_some_slot sts s Left || points_to_some_slot sts s Right then
        lemma_points_to_some_implies_has_instore_merkle_desc sts stk s
      else if add_method_of sts s = HV.BAdd then
        if HV.has_instore_merkle_desc stk k then
          lemma_has_instore_merkle_desc_implies_slot_points_to sts stk s
        else (
          assert(vsk_.valid);
          let stk_ = vsk_.st in
          let aux (ki:_)
            : Lemma (ensures (store_rel_key sts_ stk_ ki))
            = elim_key_store_rel sts stk ki;
              if ki = k then lemma_not_contains_after_bevict sts s
              else if HV.store_contains stk_ ki then (
                assert(stk_ ki = stk ki);
                let si = slot_of_key sts ki in
                assert(si <> s);
                assert(get_slot sts si = get_slot sts_ si);
                ()
              )
          in
          forall_intro aux
        )

#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit_factor 4 --query_stats"

let lemma_evictm_simulates_spec
      (#vcfg:_)
      (vs:vtls_t vcfg{vs.valid})
      (vs':_ {vtls_rel vs vs'})
      (e:logS_entry vcfg{GV.EvictM? e})
  : Lemma (requires (let st = vs.st in
                     vtls_rel vs vs' /\
                     valid_logS_entry vs e /\
                     slot_points_to_is_merkle_points_to st /\
                     merkle_points_to_uniq st /\
                     merkle_points_to_desc st))
          (ensures (let ek = to_logk_entry vs e in
                    vtls_rel (GV.verify_step e vs) (GV.verify_step ek vs')))
  = let vss = vs in
    let sts = vs.st in

    (* explicit cast needed to help resolve .st below *)
    let vsk: HV.vtls_t vcfg.app = vs' in
    let stk = vsk.st in
    let GV.EvictM s s' = e in
    (* valid log entry e implies s and s' are inuse slots *)
    assert(inuse_slot sts s /\ inuse_slot sts s');

    let k = stored_base_key sts s in
    let k' = stored_base_key sts s' in
    let vss_ = GV.verify_step e vss in
    let sts_ = vss_.st in
    let ek = to_logk_entry vss e in
    let vsk_: HV.vtls_t vcfg.app = GV.verify_step ek vsk in
    let stk_ = vsk_.st in

    if is_proper_desc k k' then

      if points_to_some_slot sts s Left || points_to_some_slot sts s Right then
        lemma_points_to_some_implies_has_instore_merkle_desc sts stk s
      else (
        let d = desc_dir k k' in
        let v' = to_merkle_value (stored_value sts s') in
        let dh' = Merkle.desc_hash v' d in
        match dh' with
        | Merkle.Empty -> ()
        | Merkle.Desc k2 h2 b2 ->
          if k2 = k then (
            if has_parent sts s && (parent_slot sts s <> s' || parent_dir sts s <> d) then (
              assert(parent_props_local sts s);
              if parent_slot sts s <> s' then (
                let sp = parent_slot sts s in
                let dp = parent_dir sts s in
                assert(points_to_dir sts sp dp s);
                let kp = stored_base_key sts sp in
                assert(kp <> k');
                assert(slot_points_to_is_merkle_points_to_local sts sp s dp);
                let vp = to_merkle_value (stored_value sts sp) in
                assert(Merkle.points_to vp dp k);
                assert(slot_points_to_is_merkle_points_to_local sts s' s d);
                assert(Merkle.points_to v' d k);
                assert(merkle_points_to_uniq_local sts sp s' k);
                ()
              )
              else (
                let od = parent_dir sts s in
                assert(points_to_dir sts s' od s);
                assert(slot_points_to_is_merkle_points_to_local sts s' s od);
                assert(Merkle.points_to v' od k);
                assert(merkle_points_to_desc_local sts s' od);
                //assert(False);
                ()
              )
            )
            else if not (has_parent sts s) && (points_to_some_slot sts s' d) then (
              let s2 = pointed_slot sts s' d in
              if s2 = s then assert(points_to_inuse_local sts s' s)
              else (
                assert(slot_points_to_is_merkle_points_to_local sts s' s2 d);
                assert(points_to_inuse_local sts s' s2);
                assert(inuse_slot sts s2);
                assert(Merkle.points_to v' d (stored_base_key sts s2));
                assert(Merkle.points_to v' d k);
                assert(k = stored_base_key sts s2);
                ()
              )
            )
            else if HV.has_instore_merkle_desc stk k then
              lemma_has_instore_merkle_desc_implies_slot_points_to sts stk s
            else (
              lemma_evictm_preserves_ismap vss e;
              assert(s <> s');
              let h = hashfn (stored_value sts s) in
              let v'_upd = Merkle.update_value v' d k h false in
              let st_upd = update_value sts s' (IntV v'_upd) in
              assert(sts_ == mevict_from_store st_upd s s' d);
              let aux (ki:_)
                : Lemma (ensures (store_rel_key sts_ stk_ ki))
                = elim_key_store_rel sts stk ki;
                  if ki = k then
                    lemma_not_contains_after_mevict st_upd s s' d
                  else if ki <> k' then (
                    if HV.store_contains stk_ ki then (
                      assert(stk_ ki = stk ki);
                      let si = slot_of_key sts ki in
                      assert(si <> s /\ si <> s');
                      assert(get_slot sts si = get_slot sts_ si);
                      ()
                    )
                  )
              in
              forall_intro aux
            )
          )
      )

let lemma_evictbm_simulates_spec
      (#vcfg:_)
      (vs:vtls_t vcfg{vs.valid})
      (vs':_ {vtls_rel vs vs'})
      (e:logS_entry vcfg{GV.EvictBM? e})
  : Lemma (requires (let st = vs.st in
                     vtls_rel vs vs' /\
                     valid_logS_entry vs e /\
                     slot_points_to_is_merkle_points_to st /\
                     merkle_points_to_uniq st /\
                     merkle_points_to_desc st))
          (ensures (let ek = to_logk_entry vs e in
                    vtls_rel (GV.verify_step e vs) (GV.verify_step ek vs')))
  = let vss = vs in
    let sts = vs.st in

    (* explicit cast needed to help resolve .st below *)
    let vsk: HV.vtls_t vcfg.app = vs' in
    let stk = vsk.st in
    let GV.EvictBM s s' t = e in

    (* otherwise valid_logS_entry would be false *)
    assert(inuse_slot sts s /\ inuse_slot sts s');

    let vss_ = GV.verify_step e vss in
    let sts_ = vss_.st in
    let ek = to_logk_entry vss e in
    let vsk_: HV.vtls_t vcfg.app = GV.verify_step ek vsk in
    let stk_ = vsk_.st in
    let k = stored_base_key sts s in
    let k' = stored_base_key sts s' in
    let open Zeta.Time in

    if k <> Root && vss.clock `ts_lt` t then
      if points_to_some_slot sts s Left || points_to_some_slot sts s Right then
        lemma_points_to_some_implies_has_instore_merkle_desc sts stk s
      else if HV.has_instore_merkle_desc stk k then
        lemma_has_instore_merkle_desc_implies_slot_points_to sts stk s
      else if add_method_of sts s = HV.MAdd && is_proper_desc k k' then
        let v' = to_merkle_value (stored_value sts s') in
        let d = desc_dir k k' in
        let dh' = Merkle.desc_hash v' d in
        match dh' with
        | Merkle.Empty -> ()
        | Merkle.Desc k2 h2 b2 ->
          if k2 = k && not b2 then (
            if not (points_to_dir sts s' d s) then (
              (* since s was added using merkle, our invariants say there is some slot that points to s *)
              let sa = pointing_slot sts s in
              assert(inuse_slot sts sa);

              (* sa points to s along direction da *)
              let da = if points_to_dir sts sa Left s then Left else Right in
              assert(points_to_dir sts sa da s);

              assert(slot_points_to_is_merkle_points_to_local sts sa s da);
              let ka = stored_base_key sts sa in
              let va = to_merkle_value (stored_value sts sa) in
              assert(Merkle.points_to va da k);
              assert(merkle_points_to_desc_local sts sa da);
              assert(not (empty_slot sts sa));
              assert(is_proper_desc k ka);
              assert(Merkle.points_to v' d k);
              assert(merkle_points_to_uniq_local sts s' sa k);
              assert(sa = s');

              ()
            )
            else (
              assert(vss_.valid && vsk_.valid);
              lemma_evictbm_preserves_ismap vss e;
              let v'_upd = Merkle.update_value v' d k h2 true in
              let sts_upd = update_value sts s' (IntV v'_upd) in
              assert(sts_ == mevict_from_store sts_upd s s' d);
              let aux (ki:_)
                : Lemma (ensures (store_rel_key sts_ stk_ ki))
                = elim_key_store_rel sts stk ki;
                  if ki = k then
                    lemma_not_contains_after_mevict sts_upd s s' d
                  else if ki <> k' then (
                    if HV.store_contains stk_ ki then (
                      assert(stk ki = stk_ ki);
                      let si = slot_of_key sts ki in
                      assert(si <> s /\ si <> s');
                      assert(get_slot sts si = get_slot sts_ si);
                      ()
                    )
                  )
              in
              forall_intro aux
            )
          )

#pop-options


let lemma_nextepoch_simulates_spec
      (#vcfg:_)
      (vs:vtls_t vcfg{vs.valid})
      (vs':_ {vtls_rel vs vs'})
  : Lemma (requires (vtls_rel vs vs' /\
                     valid_logS_entry vs GV.NextEpoch))
          (ensures (let intspec = int_verifier_spec vcfg in
                    let hispec = HV.high_verifier_spec vcfg.app in
            vtls_rel #vcfg (GV.verify_step #intspec GV.NextEpoch vs) (GV.verify_step #hispec GV.NextEpoch vs')))
  = ()

let lemma_verifyepoch_simulates_spec
      (#vcfg:_)
      (vs:vtls_t vcfg{vs.valid})
      (vs':_ {vtls_rel vs vs'})
  : Lemma (requires (vtls_rel vs vs' /\
                     valid_logS_entry vs GV.VerifyEpoch))
          (ensures (let intspec = int_verifier_spec vcfg in
                    let hispec = HV.high_verifier_spec vcfg.app in
                    vtls_rel #vcfg (GV.verify_step #intspec GV.VerifyEpoch vs)
                                   (GV.verify_step #hispec GV.VerifyEpoch vs')))
  = ()
