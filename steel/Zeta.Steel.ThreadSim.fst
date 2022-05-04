module Zeta.Steel.ThreadSim

open FStar.Classical

module M = Zeta.Merkle
module R = Zeta.Record
module KU = Zeta.Steel.KeyUtils
module TSM = Zeta.Steel.ThreadStateModel
module GK = Zeta.GenKey
module IS = Zeta.Intermediate.Store
module U32 = FStar.UInt32

let related_key_inj_1 (sk:s_base_key) (ik0 ik1:i_base_key)
  : Lemma 
    (requires
      related_base_key sk ik0 /\
      related_base_key sk ik1)
    (ensures
      ik0 == ik1)
    [SMTPat (related_base_key sk ik0);
     SMTPat (related_base_key sk ik1)]
  = KeyUtils.lift_lower_inv ik0;
    KeyUtils.lift_lower_inv ik1

#push-options "--fuel 2 --ifuel 2 --z3rlimit_factor 3 --query_stats"
 
let addm_prop (tsm: thread_state_model) (s s': T.slot_id) (r: s_record)
  : Lemma (requires (all_props tsm.store))
          (ensures (let tsm_ = vaddm tsm s s' r in
                    let a = AMP s r s' tsm in
                    (addm_precond a /\ addm_postcond a tsm_) \/
                    (tsm_.failed)))
  = let tsm_ = vaddm tsm s s' r in
    let a = AMP s r s' tsm in
    if not (check_slot_bounds s)
     || not (check_slot_bounds s')
    then
    begin
      assert(~ (addm_precond0 a));
      assert(tsm_.failed);
      ()
    end
    else
    begin
      match r with
      | ( gk, gv ) ->
      begin
        (* check store contains slot s' *)
        match get_entry tsm s' with
        | None ->
          assert (~ (addm_precond1 a));
          assert (tsm_.failed);
          ()
        | Some r' ->
          let k' = to_base_key r'.key in
          let v' = r'.value in
          let k = to_base_key gk in
          (* check k is a proper desc of k' *)
          if not (KU.is_proper_descendent k k') then
          begin
            assert (~ (addm_precond1 a));
            assert (tsm_.failed);
            ()
          end
          (* check store does not contain slot s *)
          else if Some? (get_entry tsm s) then
          begin
            assert (~ (addm_precond1 a));
            assert (tsm_.failed);
            ()
          end
          (* check v' is a merkle value *)
          else match to_merkle_value v' with
          | None -> assert (False); ()
          | Some v' ->
            let d = KU.desc_dir k k' in
            let dh' = desc_hash_dir v' d in
            let h = s_hashfn gv in

            assert (addm_precond1 a);

            match dh' with
            | T.Dh_vnone _ -> (* k' has no child in direction d *)
              // case A: of addm
              assert (addm_precond2 a);
              assert (addm_anc_points_null a);
              (* first add must be init value *)
              if not (T.eq_value gv (init_value gk)) then
              begin
                assert (addm_value_pre a =!= init_value (addm_key a));
                assert (~ (addm_precond a));
                assert (tsm_.failed);
                ()
              end
              else if TSM.points_to_some_slot tsm s' d then
              begin
                assert (tsm_.failed);
                assert (~ (addm_precond a));
                ()
              end
              else
              begin
                (* all preconditions are satisifed through case A *)
                assert (addm_precond a);
                assert (addm_value_postcond a gv);
                let tsm' = madd_to_store tsm s gk gv s' d in
                assert (madd_to_store_reqs tsm s gk gv s' d);
                lemma_madd_to_store tsm s gk gv s' d;
                let v'_upd = update_merkle_value v' d k zero false in
                assert (addm_anc_val_postcond a v'_upd);
                assert (tsm_ == update_value tsm' s' (T.MValue v'_upd));
                lemma_update_value tsm' s' (T.MValue v'_upd);
                assert (addm_anc_slot_postcond a tsm_.store);
                assert (addm_slot_postcond a tsm_.store);
                assert (~ (addm_has_desc_slot a));
                assert (identical_except2 tsm_.store tsm.store (addm_slot a) (addm_anc_slot a));
                ()
              end
            | T.Dh_vsome {T.dhd_key=k2; T.dhd_h=h2; T.evicted_to_blum = b2} ->
              if KeyUtils.eq_base_key k2 k then (* k is a child of k' *)
              begin
                // case B:
                assert (addm_anc_points_to_key a);
                (* check hashes match and k was not evicted to blum *)
                if not (KeyUtils.eq_u256 h2 h && b2 = T.Vfalse) then
                begin
                  assert (tsm_.failed);
                  assert (~ (addm_precond a));
                  ()
                end
                (* check slot s' does not contain a desc along direction d *)
                else if TSM.points_to_some_slot tsm s' d then
                begin
                  assert (tsm_.failed);
                  assert (~ (addm_precond a));
                  ()
                end
                else
                begin
                  assert (tsm_ == madd_to_store tsm s gk gv s' d);
                  lemma_madd_to_store tsm s gk gv s' d;
                  assert (addm_precond2 a);                  
                  assume (addm_precond a);
                  assert (identical_except2 tsm_.store tsm.store (addm_slot a) (addm_anc_slot a));
                  ()
                end
              end
              else if not (T.eq_value gv (init_value gk)) then
              begin
                assert (tsm_.failed);
                assert (~ (addm_precond a));
                ()
              end
              else if not (KU.is_proper_descendent k2 k) then
              begin
                assert (tsm_.failed);
                assert (~ (addm_precond a));
                ()
              end
              else
              begin
                // Case C:
                assert (addm_anc_points_to_desc a);
                let d2 = KU.desc_dir k2 k in
                assert (d2 == addm_desc_dir a);
                let Some mv = to_merkle_value gv in
                let mv_upd = update_merkle_value mv d2 k2 h2 (b2=T.Vtrue) in
                assert (addm_value_postcond a (T.MValue mv_upd));
                let v'_upd = update_merkle_value v' d k zero false in
                assert (addm_anc_val_postcond a v'_upd);
                if TSM.points_to_some_slot tsm s' d then
                begin
                  let tsm' =
                    madd_to_store_split tsm s gk (T.MValue mv_upd) s' d d2 in
                  if tsm_.failed then ()
                  else (
                    lemma_madd_to_store_split tsm s gk (T.MValue mv_upd) s' d d2;
                    assert (addm_slot_points_postcond a tsm'.store);
                    assert (addm_slot_postcond a tsm'.store);
                    assert (tsm_ == update_value tsm' s' (T.MValue v'_upd));
                    lemma_update_value tsm' s' (T.MValue v'_upd);
                    assert (addm_slot_postcond a tsm_.store);
                    assert (addm_anc_slot_postcond a tsm_.store);
                    assert (addm_has_desc_slot a);
                    assert (addm_desc_slot_postcond a tsm_.store);
                    assert (identical_except3 tsm_.store tsm.store (addm_slot a) (addm_anc_slot a) (addm_desc_slot a));
                    ()
                  )
                end
                else
                begin
                  let tsm' = madd_to_store tsm s gk (T.MValue mv_upd) s' d in
                  assert (stored_value tsm'.store s == T.MValue mv_upd);
                  assert (madd_to_store_reqs tsm s gk (T.MValue mv_upd) s' d);
                  lemma_madd_to_store tsm s gk (T.MValue mv_upd) s' d;

                  assert (tsm_ == update_value tsm' s' (T.MValue v'_upd));
                  lemma_update_value tsm' s' (T.MValue v'_upd);
                  assert (addm_slot_postcond a tsm_.store);
                  assert (addm_anc_slot_postcond a tsm_.store);
                  assert (~ (addm_has_desc_slot a));
                  ()
                end
              end
      end
    end

#pop-options

#push-options "--fuel 1 --ifuel 1 --query_stats"

let addm_simulation (tsm: s_thread_state) (i_tsm: i_thread_state) (se: s_log_entry) (ie: i_log_entry)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_log_entry se ie /\
                     LT.AddM? se /\ not tsm.failed))
          (ensures (let LT.AddM s s' r = se in
                    let GV.AddM ir is is' = ie in
                    let tsm_ = vaddm tsm s s' r in
                    let i_tsm_ = IV.addm ir is is' i_tsm in
                    (not tsm_.failed) ==> related_tsm tsm_ i_tsm_))
  = let LT.AddM s s' r = se in
    let GV.AddM ir is is' = ie in
    let a = AMP s r s' tsm in
    let i_a = IV.AMP is ir is' i_tsm in

    lemma_related_implies_all_props tsm.store i_tsm.IV.st;
    addm_prop tsm s s' r;

    let tsm_ = vaddm tsm s s' r in
    if not tsm_.failed then
    begin
      assert (addm_precond a /\ addm_postcond a tsm_);
      assert (related_addm_param a i_a);

      let i_tsm_ = IV.addm ir is is' i_tsm in
      assert (IV.addm_precond i_a /\ IV.addm_postcond i_a i_tsm_);

      related_addm_postcond a i_a tsm_ i_tsm_;
      ()
    end

#pop-options

let related_badd_to_store
  (tsm: s_thread_state) (s: T.slot {empty_slot tsm.store s}) (k: T.key) (v: T.value{LT.is_value_of k v})
  (i_st: i_store) (i_s: i_slot_id {IS.empty_slot i_st i_s}) (i_r: i_record)
  : Lemma (requires (let i_k, i_v = i_r in
                     related_store tsm.store i_st /\ related_slot s i_s /\
                     related_key k i_k /\
                     related_val v i_v))
            (ensures (let tsm_ = put_entry tsm s (mk_entry k v BAdd) in
                    let i_st_ = IS.badd_to_store i_st i_s i_r in
                    related_store tsm_.store i_st_))
  = let i_k, i_v = i_r in
    let tsm_ = put_entry tsm s (mk_entry k v BAdd) in
    let st_ = tsm_.store in
    let st = tsm.store in
    let i_st_ = IS.badd_to_store i_st i_s i_r in

    let aux (i:_)
      : Lemma (ensures (related_store_entry_opt (Seq.index st_ i) (Seq.index i_st_ i)))
      = if i_s <> i then
        begin
          eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
          with i;

          assert (IS.identical_except i_st i_st_ i_s);

          eliminate forall s'. s' <> i_s ==> IS.get_slot i_st s' = IS.get_slot i_st_ s'
          with i
        end
    in
    forall_intro aux

#push-options "--fuel 2 --ifuel 2 --query_stats"

let addb_simulation (tsm: s_thread_state) (i_tsm: i_thread_state) (se: s_log_entry) (ie: i_log_entry)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_log_entry se ie /\
                     LT.AddB? se /\ not tsm.failed))
          (ensures (let LT.AddB s t tid r = se in
                    let GV.AddB i_r i_s i_t i_tid = ie in
                    let tsm_ = vaddb tsm s t tid r  in
                    let i_tsm_ = IV.addb i_r i_s i_t i_tid i_tsm in
                    (not tsm_.failed) ==> related_tsm tsm_ i_tsm_))
  = let T.AddB s t thread_id r = se in
    let st = tsm.store in
    let tsm_ = vaddb tsm s t thread_id r in

    let GV.AddB i_r i_s i_t i_tid = ie in
    let (i_k, i_v) = i_r in
    let i_st = i_tsm.IV.st in
    let i_tsm_ = IV.addb i_r i_s i_t i_tid i_tsm in

    assert (related_store st i_st);

    if not tsm_.failed then
    begin
      assert (check_slot_bounds s);

      match r with
      | ( k, v ) ->

        assert (not (is_root_key k));
        assert (not (Some? (get_entry tsm s)));

        assert (related_key k i_k);
        related_root k i_k;
        assert (i_k <> GK.IntK Zeta.BinTree.Root);

        assert (related_slot s i_s);

        eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
        with i_s;

        assert (not (IS.inuse_slot i_st i_s));

        let tsm1 = update_hadd tsm (epoch_of_timestamp t) (k, v) t thread_id in
        assert (related_tsm tsm1 i_tsm);

        match next t with
        | Some t' ->
          let i_t' = Zeta.Time.next i_t in

          related_next t i_t;
          assert (related_timestamp t' i_t');

          related_max tsm1.clock t' i_tsm.clock i_t';
          let tsm2 = update_clock tsm1 (max tsm1.clock t') in
          let i_tsm2 = IV.update_thread_clock i_tsm (Zeta.Time.max i_tsm.clock i_t') in
          assert (related_tsm tsm2 i_tsm2);

          assert (tsm_ == put_entry tsm2 s (mk_entry k v BAdd));
          let i_st3 = IS.badd_to_store i_st i_s i_r in
          assert (i_tsm_ == IV.update_thread_store i_tsm2 i_st3);
          related_badd_to_store tsm2 s k v i_st i_s i_r;
          assert (related_store tsm_.store i_st3);
          ()
    end

#pop-options

#push-options "--fuel 1 --ifuel 1 --query_stats"

module U16 = FStar.UInt16

let related_update_value (tsm: s_thread_state)
                         (s: T.slot {has_slot tsm s})
                         (v: T.value {LT.is_value_of (key_of_slot tsm s) v})
                         (i_st: i_store)
                         (i_s: i_slot_id {IS.inuse_slot i_st i_s})
                         (i_v: i_val{R.compatible (IS.stored_key i_st i_s) i_v})
  : Lemma (requires (let st = tsm.store in
                     related_store st i_st /\
                     related_slot s i_s /\
                     related_val v i_v))
          (ensures (let tsm_ = update_value tsm s v in
                    let st_ = tsm_.store in
                    let i_st_ = IS.update_value i_st i_s i_v in
                    related_store st_ i_st_))
  = let st = tsm.store in
    let tsm_ = update_value tsm s v in
    let st_ = tsm_.store in
    let i_st_ = IS.update_value i_st i_s i_v in

    eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
    with i_s;

    lemma_update_value tsm s v;
    assert (identical_except st st_ s);
    assert (IS.identical_except i_st i_st_ i_s);

    let aux (i:_)
      : Lemma (ensures (related_store_entry_opt (Seq.index st_ i) (Seq.index i_st_ i)))
      = if i <> i_s then
        begin
          eliminate forall (s': T.slot). s' <> s ==> get_slot st s' == get_slot st_ s'
          with (U16.uint_to_t i);

          eliminate forall (s': i_slot_id). s' <> i_s ==> IS.get_slot i_st s' = IS.get_slot i_st_ s'
          with i
        end
    in
    forall_intro aux

#pop-options

#push-options "--fuel 1 --ifuel 1 --query_stats"

let related_mevict_from_store (tsm: s_thread_state)
                              (s: T.slot)
                              (s': T.slot)
                              (d: bool)
                              (i_st: i_store)
                              (i_s: IS.inuse_slot_id i_st )
                              (i_s': IS.inuse_slot_id i_st)
                              (i_d: i_dir)
  : Lemma (requires (let st = tsm.store in
                     IS.points_to_none i_st i_s Zeta.BinTree.Left /\
                     IS.points_to_none i_st i_s Zeta.BinTree.Right /\
                     i_s <> i_s' /\
                     (not (IS.has_parent i_st i_s) /\ IS.points_to_none i_st i_s' i_d \/
                      IS.has_parent i_st i_s /\ IS.parent_slot i_st i_s = i_s' /\ IS.parent_dir i_st i_s = i_d) /\
                     related_store st i_st /\
                     related_slot s i_s /\
                     related_slot s' i_s' /\
                     related_desc_dir d i_d))
            (ensures (let tsm_ = mevict_from_store tsm s s' d in
                      let st_ = tsm_.store in
                      let i_st_ = IS.mevict_from_store i_st i_s i_s' i_d in
                      related_store st_ i_st_))
  = let st = tsm.store in
    let tsm_ = mevict_from_store tsm s s' d in
    let st_ = tsm_.store in
    let i_st_ = IS.mevict_from_store i_st i_s i_s' i_d in

    (* slot s/i_s entries are related *)
    eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
    with i_s;

    (* slot s'/i_s' entries are related *)
    eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
    with i_s';

    lemma_mevict_from_store tsm s s' d;

    let aux (i:_)
      : Lemma (ensures (related_store_entry_opt (Seq.index st_ i) (Seq.index i_st_ i)))
      = if i <> i_s && i <> i_s' then
        begin
          eliminate forall (s2: T.slot). s2 <> s ==> s2 <> s' ==> get_slot st s2 == get_slot st_ s2
          with (U16.uint_to_t i);

          eliminate forall (s': i_slot_id). s' <> i_s ==> s' <> i_s' ==> IS.get_slot i_st s' = IS.get_slot i_st_ s'
          with i
        end
    in
    forall_intro aux

#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit_factor 3 --query_stats"

let evictm_simulation (tsm: s_thread_state) (i_tsm: i_thread_state) (se: s_log_entry) (ie: i_log_entry)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_log_entry se ie /\
                     LT.EvictM? se /\ not tsm.failed))
          (ensures (let LT.EvictM p = se in
                    let GV.EvictM i_s i_s' = ie in
                    let tsm_ = vevictm tsm p.s p.s_  in
                    let i_tsm_ = IV.evictm i_s i_s' i_tsm in
                    (not tsm_.failed) ==> related_tsm tsm_ i_tsm_))
  = let T.EvictM p = se in
    let s: T.slot_id = p.s in
    let s': T.slot_id = p.s_ in
    let GV.EvictM i_s i_s' = ie in
    let tsm_ = vevictm tsm s s' in
    let i_tsm_ = IV.evictm i_s i_s' i_tsm in

    let st = tsm.store in
    let i_st = i_tsm.IV.st in
    assert (related_store st i_st);
    assert (related_slot s i_s /\ related_slot s' i_s');

    eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
    with i_s;

    eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
    with i_s';

    if not tsm_.failed then
    begin
      assert (check_slot_bounds s);
      assert (check_slot_bounds s');
      assert (s <> s');

      match get_entry tsm s,
            get_entry tsm s'
      with
      | Some r, Some r' ->
        assert (~ (IS.empty_slot i_st i_s) /\ ~ (IS.empty_slot i_st i_s'));
        assert (i_s <> i_s');

        let gk = r.key in
        let i_gk = IS.stored_key i_st i_s in
        assert (related_key gk i_gk);

        let v = r.value in
        let i_v = IS.stored_value i_st i_s in
        assert (related_val v i_v);

        let gk' = r'.key in
        let v' = r'.value in
        let i_v' = IS.stored_value i_st i_s' in
        assert (related_val v' i_v');

        let k = to_base_key gk in
        let i_k = IS.stored_base_key i_st i_s in
        lemma_related_base_key gk i_gk;
        assert (related_base_key k i_k);


        let k' = to_base_key gk' in
        let i_k' = IS.stored_base_key i_st i_s' in
        lemma_related_base_key gk' (IS.stored_key i_st i_s');
        assert (related_base_key k' i_k');

        assert (KU.is_proper_descendent k k');
        lemma_related_key_proper_descendent k k' i_k i_k';
        assert (Zeta.BinTree.is_proper_desc i_k i_k');

        assert (not (TSM.points_to_some_slot tsm s true) &&
                not (TSM.points_to_some_slot tsm s false));
        assert (not (IS.points_to_some_slot i_st i_s Zeta.BinTree.Left));
        assert (not (IS.points_to_some_slot i_st i_s Zeta.BinTree.Right));

        let d = KU.desc_dir k k' in
        let i_d = Zeta.BinTree.desc_dir i_k i_k' in
        assert (related_desc_dir d i_d);

        let Some v' = to_merkle_value v' in
        let i_v' = R.to_merkle_value i_v' in
        assert (related_mval v' i_v');

        let dh' = desc_hash_dir v' d in
        let i_dh' = M.desc_hash i_v' i_d in
        assert (related_desc_hash dh' i_dh');

        let h = s_hashfn v in
        let i_h = Zeta.HashFunction.hashfn i_v in
        related_hashfn v i_v;
        assert (related_hash_value h i_h);

        match dh', i_dh' with
        | T.Dh_vsome {T.dhd_key=k2; T.dhd_h=h2; T.evicted_to_blum = b2},
          M.Desc i_k2 i_h2 i_b2 ->
          assert (related_base_key k2 i_k2);
          assert (related_hash_value h2 i_h2);
          assert (T.Vtrue? b2 == i_b2);

          (* all checks at intermediate layer pass ... *)
          assert (i_tsm_.IV.valid);

          let v'_upd = update_merkle_value v' d k h false in
          let i_v'_upd = M.update_value i_v' i_d i_k i_h false in
          assert (related_mval v'_upd i_v'_upd);

          let tsm1 = update_value tsm s' (T.MValue v'_upd) in
          lemma_update_value tsm s' (T.MValue v'_upd);
          let i_st1 = IS.update_value i_st i_s' (R.IntV i_v'_upd) in
          related_update_value tsm s' (T.MValue v'_upd) i_st i_s' (R.IntV i_v'_upd);
          assert (related_store tsm1.store i_st1);

          assert (tsm_ == mevict_from_store tsm1 s s' d);

          let i_st2 = IS.mevict_from_store i_st1 i_s i_s' i_d in
          assert (i_tsm_ == IV.update_thread_store i_tsm i_st2);
          related_mevict_from_store tsm1 s s' d i_st1 i_s i_s' i_d;
          ()
    end

#pop-options

let related_sat_evictb_checks (tsm: s_thread_state)
                              (s: T.slot)
                              (t: s_timestamp)
                              (i_tsm: i_thread_state)
                              (i_s: i_slot_id)
                              (i_t: i_timestamp)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_slot s i_s /\
                     related_timestamp t i_t /\
                     sat_evictb_checks tsm s t /\
                     not tsm.failed))
          (ensures (IV.sat_evictb_checks i_s i_t i_tsm))
  = let st = tsm.store in
    let i_st = i_tsm.IV.st in

    eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
    with i_s;

    assert (inuse_slot st s);
    assert (IS.inuse_slot i_st i_s);

    match get_entry tsm s with
    | Some r ->
      let k = r.key in
      let i_k = IS.stored_key i_st i_s in
      assert (related_key k i_k);

      assert (not (is_root_key k));
      related_root k i_k;
      assert (i_k <> GK.IntK Zeta.BinTree.Root);

      let clock = tsm.clock in
      let i_clock = i_tsm.IV.clock in
      assert (related_timestamp clock i_clock);

      assert (clock `timestamp_lt` t);
      related_timestamp_lt clock t i_clock i_t;
      assert (i_clock `Zeta.Time.ts_lt` i_t);
      ()

#push-options "--fuel 1 --ifuel 1 --query_stats"

module HV = Zeta.High.Verifier

let related_vevictb_update_hash_clock (tsm: s_thread_state)
                                      (s: T.slot)
                                      (t: s_timestamp)
                                      (i_tsm: i_thread_state)
                                      (i_s: i_slot_id)
                                      (i_t: i_timestamp)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_slot s i_s /\
                     related_timestamp t i_t /\
                     sat_evictb_checks tsm s t /\
                     not tsm.failed))
          (ensures (let tsm_ = vevictb_update_hash_clock tsm s t in
                    IV.sat_evictb_checks i_s i_t i_tsm /\
                    (let i_tsm_ = IV.vevictb_update_hash_clock i_s i_t i_tsm in
                     related_tsm tsm_ i_tsm_)))
  = related_sat_evictb_checks tsm s t i_tsm i_s i_t;
    let st = tsm.store in
    let i_st = i_tsm.IV.st in
    let tsm_ = vevictb_update_hash_clock tsm s t in
    let i_tsm_ = IV.vevictb_update_hash_clock i_s i_t i_tsm in

    eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
    with i_s

let related_bevict_from_store (tsm: s_thread_state)
                              (s: T.slot)
                              (i_st: i_store)
                              (i_s: i_slot_id)
  : Lemma (requires (let st = tsm.store in
                     IS.inuse_slot i_st i_s /\
                     IS.points_to_none i_st i_s Zeta.BinTree.Left /\
                     IS.points_to_none i_st i_s Zeta.BinTree.Right /\
                     IS.add_method_of i_st i_s = HV.BAdd /\
                     related_store st i_st /\
                     related_slot s i_s))
           (ensures (let tsm_ = bevict_from_store tsm s in
                     let st_ = tsm_.store in
                     let i_st_ = IS.bevict_from_store i_st i_s in
                     related_store st_ i_st_))
  = let st = tsm.store in
    let tsm_ = bevict_from_store tsm s in
    let st_ = tsm_.store in
    let i_st_ = IS.bevict_from_store i_st i_s in

    (* slot s/i_s entries are related *)
    eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
    with i_s;

    lemma_bevict_from_store tsm s;

    let aux (i:_)
      : Lemma (ensures (related_store_entry_opt (Seq.index st_ i) (Seq.index i_st_ i)))
      = if i <> i_s then
        begin
          eliminate forall (s2: T.slot). s2 <> s ==> get_slot st s2 == get_slot st_ s2
          with (U16.uint_to_t i);

          eliminate forall (s': i_slot_id). s' <> i_s ==> IS.get_slot i_st s' = IS.get_slot i_st_ s'
          with i
        end
    in
    forall_intro aux

#push-options "--z3rlimit_factor 3"

let evictb_simulation (tsm: s_thread_state) (i_tsm: i_thread_state) (se: s_log_entry) (ie: i_log_entry)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_log_entry se ie /\
                     T.EvictB? se /\ not tsm.failed))
          (ensures (let T.EvictB p = se in
                    let GV.EvictB i_s i_t = ie in
                    let tsm_ = vevictb tsm p.s p.t in
                    let i_tsm_ = IV.evictb i_s i_t i_tsm in
                    (not tsm_.failed) ==> related_tsm tsm_ i_tsm_))
  = let T.EvictB p = se in
    let s: T.slot_id = p.s in
    let t = p.t in
    let tsm_ = vevictb tsm s t in

    let GV.EvictB i_s i_t = ie in
    let i_tsm_ = IV.evictb i_s i_t i_tsm in

    let st = tsm.store in
    let i_st = i_tsm.IV.st in
    assert (related_store st i_st);

    assert (related_slot s i_s);
    assert (related_timestamp t i_t);

    eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
    with i_s;

    if not tsm_.failed then
    begin
      assert (check_slot_bounds s);
      assert (sat_evictb_checks tsm s t);
      related_sat_evictb_checks tsm s t i_tsm i_s i_t;
      assert (IV.sat_evictb_checks i_s i_t i_tsm);

      let Some r = get_entry tsm s in
      assert (r.add_method = BAdd);

      assert (IS.add_method_of i_st i_s = HV.BAdd);
      let tsm1 = vevictb_update_hash_clock tsm s t in
      let i_tsm1 = IV.vevictb_update_hash_clock i_s i_t i_tsm in

      related_vevictb_update_hash_clock tsm s t i_tsm i_s i_t;
      assert (related_tsm tsm1 i_tsm1);

      assert (tsm_ == bevict_from_store tsm1 s);
      assert (i_tsm1.IV.st == i_st);

      let i_st1 = IS.bevict_from_store i_st i_s in
      assert (i_tsm_ == IV.update_thread_store i_tsm1 i_st1);

      related_bevict_from_store tsm1 s i_st i_s;

      assert (related_store tsm_.store i_st1);
      ()
    end

#pop-options
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit_factor 3 --query_stats"

let evictbm_simulation (tsm: s_thread_state) (i_tsm: i_thread_state) (se: s_log_entry) (ie: i_log_entry)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_log_entry se ie /\
                     T.EvictBM? se /\ not tsm.failed))
          (ensures (let T.EvictBM p = se in
                    let GV.EvictBM i_s i_s' i_t = ie in
                    let tsm_ = vevictbm tsm p.s p.s_ p.t in
                    let i_tsm_ = IV.evictbm i_s i_s' i_t i_tsm in
                    (not tsm_.failed) ==> related_tsm tsm_ i_tsm_))
  = let T.EvictBM p = se in
    let s: T.slot_id = p.s in
    let s': T.slot_id = p.s_ in
    let t = p.t in
    let tsm_ = vevictbm tsm s s' t in

    let GV.EvictBM i_s i_s' i_t = ie in
    let i_tsm_ = IV.evictbm i_s i_s' i_t i_tsm in

    let st = tsm.store in
    let i_st = i_tsm.IV.st in
    assert (related_store st i_st);
    assert (related_slot s i_s /\ related_slot s' i_s');

    eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
    with i_s;

    eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
    with i_s';

    if not tsm_.failed then
    begin
      assert (check_slot_bounds s);
      assert (check_slot_bounds s');
      assert (s <> s');

      assert (i_s <> i_s');

      assert (sat_evictb_checks tsm s t);
      related_sat_evictb_checks tsm s t i_tsm i_s i_t;
      assert (IV.sat_evictb_checks i_s i_t i_tsm);

      let Some r = get_entry tsm s in
      let Some r' = get_entry tsm s' in

      assert (r.add_method = MAdd);
      assert (IS.add_method_of i_st i_s = HV.MAdd);
      assert (not (IS.empty_slot i_st i_s'));

      let gk = r.key in
      let i_gk = IS.stored_key i_st i_s in
      assert (related_key gk i_gk);

      let gk' = r'.key in
      let i_gk' = IS.stored_key i_st i_s' in
      assert (related_key gk' i_gk');

      let v' = r'.value in
      let i_v' = IS.stored_value i_st i_s' in
      assert (related_val v' i_v');

      let k = to_base_key gk in
      let i_k = IS.stored_base_key i_st i_s in
      lemma_related_base_key gk i_gk;
      assert (related_base_key k i_k);

      let k' = to_base_key gk' in
      let i_k' = IS.stored_base_key i_st i_s' in
      lemma_related_base_key gk' (IS.stored_key i_st i_s');
      assert (related_base_key k' i_k');

      assert (KU.is_proper_descendent k k');
      lemma_related_key_proper_descendent k k' i_k i_k';
      assert (Zeta.BinTree.is_proper_desc i_k i_k');

      let Some mv' = to_merkle_value v' in
      let i_mv' = R.to_merkle_value i_v' in
      assert (related_mval mv' i_mv');

      let d = KU.desc_dir k k' in
      let i_d = Zeta.BinTree.desc_dir i_k i_k' in
      assert (related_desc_dir d i_d);

      let dh' = desc_hash_dir mv' d in
      let i_dh' = M.desc_hash i_mv' i_d in
      assert (related_desc_hash dh' i_dh');
      match dh', i_dh' with
      | T.Dh_vsome {T.dhd_key=k2; T.dhd_h=h2; T.evicted_to_blum = b2},
        M.Desc i_k2 i_h2 i_b2 ->
        assert (related_base_key k2 i_k2);
        assert (related_hash_value h2 i_h2);
        assert (T.Vtrue? b2 == i_b2);

        assert (k2 == k /\ b2 = T.Vfalse);
        assert (i_k2 == i_k /\ not i_b2);

        assert (i_tsm_.IV.valid);

        let tsm1 = vevictb_update_hash_clock tsm s t in
        let i_tsm1 = IV.vevictb_update_hash_clock i_s i_t i_tsm in

        related_vevictb_update_hash_clock tsm s t i_tsm i_s i_t;
        assert (related_tsm tsm1 i_tsm1);

        let mv'_upd = update_merkle_value mv' d k h2 true in
        let i_mv'_upd = M.update_value i_mv' i_d i_k i_h2 true in
        assert (related_mval mv'_upd i_mv'_upd);

        let tsm2 = update_value tsm1 s' (T.MValue mv'_upd) in
        let i_st2 = IS.update_value i_st i_s' (R.IntV i_mv'_upd)  in
        related_update_value tsm1 s' (T.MValue mv'_upd) i_st i_s' (R.IntV i_mv'_upd);
        assert (related_store tsm2.store i_st2);

        assert (tsm_ == mevict_from_store tsm2 s s' d);
        let i_st3 = IS.mevict_from_store i_st2 i_s i_s' i_d in
        assert (i_tsm_ == IV.update_thread_store i_tsm1 i_st3);

        related_mevict_from_store tsm2 s s' d i_st2 i_s i_s' i_d;

        ()
    end


#pop-options

#push-options "--fuel 1 --ifuel 1 --query_stats"

let nextepoch_simulation (tsm: s_thread_state) (i_tsm: i_thread_state) (se: s_log_entry) (ie: i_log_entry)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_log_entry se ie /\
                     T.NextEpoch? se /\ not tsm.failed))
          (ensures (let tsm_ = nextepoch tsm in
                    let i_tsm_ = IV.nextepoch i_tsm in
                    (not tsm_.failed) ==> related_tsm tsm_ i_tsm_))
  = let tsm_ = nextepoch tsm in
    let i_tsm_ = IV.nextepoch i_tsm in

    let c = tsm.clock in
    let i_c = i_tsm.IV.clock in
    assert (related_timestamp c i_c);

    let e = epoch_of_timestamp c in
    let i_e = i_c.Zeta.Time.e in
    related_timestamp_epoch c i_c;
    assert (related_epoch e i_e);

    if not tsm_.failed then
    begin
      related_epoch_incr e i_e;
      let e1 = U32.add e U32.one in
      let i_e1 = i_e + 1 in
      assert (related_epoch e1 i_e1);
      related_epoch_shift e1 i_e1;

      ()
    end

#pop-options

let verifyepoch_simulation (tsm: s_thread_state) (i_tsm: i_thread_state) (se: s_log_entry) (ie: i_log_entry)
  : Lemma (requires (related_tsm tsm i_tsm /\
                     related_log_entry se ie /\
                     T.VerifyEpoch? se /\ not tsm.failed))
          (ensures (let tsm_ = verifyepoch tsm in
                    let i_tsm_ = IV.verifyepoch i_tsm in
                    (not tsm_.failed) ==> related_tsm tsm_ i_tsm_))
  = ()
