module Zeta.Steel.AddMRel

open FStar.Classical

module M = Zeta.Merkle
module GK = Zeta.GenKey
module R = Zeta.Record
module T = Zeta.Steel.FormatsManual
module SS = Zeta.Steel.StoreRel
module IV = Zeta.Intermediate.Verifier
module IS = Zeta.Intermediate.Store
module U16 = FStar.UInt16

let related_addm_precond1 (a: addm_param) (i_a: i_addm_param)
  : Lemma (requires (related_addm_param a i_a /\ addm_precond1 a))
          (ensures (IV.addm_precond1 i_a))
          [SMTPat (related_addm_param a i_a)]
  = let AMP s p s' tsm = a in
    let st = addm_store_pre a in
    let IV.AMP i_s (i_k, i_v) i_s' i_tsm = i_a in
    let i_st = IV.addm_store_pre i_a in

    assert(related_store st i_st);
    lemma_related_implies_all_props st i_st;

    eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
    with i_s;

    eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
    with i_s';

    (* s <> s' ==> *)
    assert (i_s <> i_s');

    assert (IS.inuse_slot i_st i_s');
    assert (IS.empty_slot i_st i_s);

    (* ancestor keys are related *)
    assert (related_key (stored_key st s') (IS.stored_key i_st i_s'));
    lemma_related_base_key (stored_key st s') (IS.stored_key i_st i_s');

    let k' = stored_base_key st s' in
    let i_k' = IS.stored_base_key i_st i_s' in
    assert (related_base_key k' i_k');

    let gk = addm_key a in
    let bk = to_base_key gk in
    let i_gk = IV.addm_key i_a in
    let i_bk = GK.to_base_key i_gk in
    assert (related_key gk i_gk);
    lemma_related_base_key gk i_gk;

    assert (is_proper_descendent bk k');
    lemma_related_key_proper_descendent bk k' i_bk i_k';
    assert (Zeta.BinTree.is_proper_desc i_bk i_k');
    ()

let related_addm_base_key (a: addm_param) (i_a: i_addm_param)
  : Lemma (requires (related_addm_param a i_a))
          (ensures (related_base_key (addm_base_key a) (IV.addm_base_key i_a)))
          [SMTPat (related_addm_param a i_a)]
  = let gk = addm_key a in
    let i_gk = IV.addm_key i_a in
    lemma_related_base_key gk i_gk

let related_addm_anc (a: addm_param) (i_a: i_addm_param)
   : Lemma (requires (related_addm_param a i_a /\ addm_precond1 a))
           (ensures (related_base_key (addm_anc_key a) (IV.addm_anc_key i_a) /\
                     related_mval (addm_anc_val_pre a) (IV.addm_anc_val_pre i_a) /\
                     related_desc_dir (addm_dir a) (IV.addm_dir i_a)))
           [SMTPat (related_addm_param a i_a)]
  = let AMP s p s' tsm = a in
    let st = addm_store_pre a in
    let IV.AMP i_s (i_k, i_v) i_s' i_tsm = i_a in
    let i_st = IV.addm_store_pre i_a in

    assert(related_store st i_st);

    eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
    with i_s';

    (* ancestor keys are related *)
    assert (related_key (stored_key st s') (IS.stored_key i_st i_s'));
    lemma_related_base_key (stored_key st s') (IS.stored_key i_st i_s');

    let bk = addm_base_key a in
    let i_bk = IV.addm_base_key i_a in
    lemma_related_base_key (addm_key a) (IV.addm_key i_a);
    assert (related_base_key bk i_bk);

    let k' = addm_anc_key a in
    let i_k' = IV.addm_anc_key i_a in
    assert (related_base_key k' i_k');

    assert (related_mval (addm_anc_val_pre a) (IV.addm_anc_val_pre i_a));
    assert (is_proper_descendent bk k');
    lemma_related_key_proper_descendent bk k' i_bk i_k'

let related_anc_points_to (a: addm_param) (i_a: i_addm_param)
   : Lemma (requires (related_addm_param a i_a /\ addm_precond2 a))
           (ensures (let mv' = addm_anc_val_pre a in
                     let d = addm_dir a in
                     let i_mv' = IV.addm_anc_val_pre i_a in
                     let i_d = IV.addm_dir i_a in

                     mv_points_to_some mv' d ==>
                     (M.points_to_some i_mv' i_d /\
                      Zeta.BinTree.is_desc (M.pointed_key i_mv' i_d) (IV.addm_base_key i_a))))
           [SMTPat (related_addm_param a i_a)]
  = let mv' = addm_anc_val_pre a in
    let d = addm_dir a in
    let i_mv' = IV.addm_anc_val_pre i_a in
    let i_d = IV.addm_dir i_a in
    let k = addm_base_key a in
    let i_k = IV.addm_base_key i_a in
    let open Zeta.BinTree in

    if mv_points_to_some mv' d then
    begin
      assert (M.points_to_some i_mv' i_d);
      let kd = mv_pointed_key mv' d in
      let i_kd = M.pointed_key i_mv' i_d in

      assert (k = kd \/ is_proper_descendent kd k);
      assert (related_base_key kd i_kd);

      if k = kd then
        lemma_desc_reflexive i_kd
      else
      begin
        assert (i_k <> i_kd);
        assert (is_proper_descendent kd k);
        lemma_related_key_proper_descendent kd k i_kd i_k
      end
    end

let related_addm_precond2 (a: addm_param) (i_a: i_addm_param)
   : Lemma (requires (related_addm_param a i_a /\ addm_precond2 a))
           (ensures (IV.addm_precond2 i_a))
           [SMTPat (related_addm_param a i_a)]
  = ()

let related_addm_caseA (a: addm_param) (i_a: i_addm_param)
   : Lemma (requires (related_addm_param a i_a /\ addm_precond2 a /\ addm_anc_points_null a))
           (ensures (IV.addm_anc_points_null i_a))
           [SMTPat (related_addm_param a i_a)]
   = ()

let related_addm_caseB (a: addm_param) (i_a: i_addm_param)
   : Lemma (requires (related_addm_param a i_a /\ addm_precond2 a /\ addm_anc_points_to_key a))
           (ensures (IV.addm_anc_points_to_key i_a))
           [SMTPat (related_addm_param a i_a)]
   = ()

let related_addm_caseC (a: addm_param) (i_a: i_addm_param)
   : Lemma (requires (related_addm_param a i_a /\ addm_precond2 a /\ addm_anc_points_to_desc a))
           (ensures (IV.addm_anc_points_to_desc i_a))
           [SMTPat (related_addm_param a i_a)]
   = ()

let related_addm_desc (a: addm_param) (i_a: i_addm_param)
  : Lemma (requires (related_addm_param a i_a /\ addm_precond2 a /\ addm_anc_points_to_desc a))
           (ensures (let kd = addm_desc a in
                     let k = addm_base_key a in
                     let d2 = addm_desc_dir a in
                     let i_k = IV.addm_base_key i_a in
                     let i_kd = IV.addm_desc i_a in
                     let i_d2 = IV.addm_desc_dir i_a in
                     related_base_key kd i_kd /\
                     related_desc_dir d2 i_d2))
           [SMTPat (related_addm_param a i_a)]
  = lemma_related_key_proper_descendent (addm_desc a) (addm_base_key a)
                                        (IV.addm_desc i_a) (IV.addm_base_key i_a)

let related_addm_precond_caseA (a: addm_param) (i_a: i_addm_param)
  : Lemma (requires (related_addm_param a i_a /\ addm_precond a /\ addm_anc_points_null a))
          (ensures (let i_st = IV.addm_store_pre i_a in
                    let i_s' = IV.addm_anc_slot i_a in
                    let i_d = IV.addm_dir i_a in
                    IV.addm_value_pre i_a = R.init_value (IV.addm_key i_a) /\
                    IS.points_to_none i_st i_s' i_d))
           [SMTPat (related_addm_param a i_a)]
  = let st = addm_store_pre a in
    let s' = addm_anc_slot a in
    let d = addm_dir a in

    assert (addm_value_pre a = init_value (addm_key a));
    assert (points_to_none st s' d);

    let i_st = IV.addm_store_pre i_a in
    let i_s' = IV.addm_anc_slot i_a in
    let i_d = IV.addm_dir i_a in

    assert (related_store st i_st);
    assert (related_slot s' i_s');
    assert (related_desc_dir d i_d);
    assert (related_val (addm_value_pre a) (IV.addm_value_pre i_a));
    related_init_value (addm_key a) (IV.addm_key i_a);
    assert(IV.addm_value_pre i_a = R.init_value (IV.addm_key i_a));

    eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
    with i_s';
    ()

let related_addm_precond_caseB (a: addm_param) (i_a: i_addm_param)
  : Lemma (requires (related_addm_param a i_a /\ addm_precond a /\ addm_anc_points_to_key a))
          (ensures (let i_st = IV.addm_store_pre i_a in
                    let i_s' = IV.addm_anc_slot i_a in
                    let i_d = IV.addm_dir i_a in
                    IV.addm_desc_hash_dir i_a = M.Desc (IV.addm_base_key i_a) (IV.addm_hash_val_pre i_a) false /\
                    IS.points_to_none i_st i_s' i_d))
           [SMTPat (related_addm_param a i_a)]
  = let st = addm_store_pre a in
    let s' = addm_anc_slot a in
    let d = addm_dir a in
    let dh = addm_desc_hash_dir a in

    let i_st = IV.addm_store_pre i_a in
    let i_s' = IV.addm_anc_slot i_a in
    let i_d = IV.addm_dir i_a in
    let i_dh = IV.addm_desc_hash_dir i_a in

    assert (related_desc_hash dh i_dh);
    assert (related_val (addm_value_pre a) (IV.addm_value_pre i_a));
    related_hashfn (addm_value_pre a) (IV.addm_value_pre i_a);
    ()

let related_addm_precond_caseC (a: addm_param) (i_a: i_addm_param)
  : Lemma (requires (related_addm_param a i_a /\ addm_precond a /\ addm_anc_points_to_desc a))
          (ensures (IV.addm_value_pre i_a = R.init_value (IV.addm_key i_a)))
           [SMTPat (related_addm_param a i_a)]
  = related_init_value (addm_key a) (IV.addm_key i_a)

let related_addm_precond (a: addm_param) (i_a: i_addm_param)
  : Lemma (requires (related_addm_param a i_a /\ addm_precond a))
          (ensures (IV.addm_precond i_a))
  = ()

let related_addm_value (a: addm_param {addm_precond a})
                       (i_a: i_addm_param)
                       (v: T.value {is_value_of (addm_key a) v})
                       (i_v: i_val {R.compatible (IV.addm_key i_a) i_v})
  : Lemma (requires (related_addm_param a i_a /\
                     addm_value_postcond a v /\
                     IV.addm_value_postcond i_a i_v))
          (ensures related_val v i_v)
  = ()

let related_addm_slot_points (a: addm_param)
                             (i_a: i_addm_param)
                             (st_: contents)
                             (i_st_: i_store)
  : Lemma (requires (related_addm_param a i_a /\ addm_precond a /\
                     addm_slot_postcond a st_ /\
                     IV.addm_slot_postcond i_a i_st_))
          (ensures (let s = addm_slot a  in
                    let i_s = IV.addm_slot i_a  in
                    let Some e = Seq.index st_ i_s in
                    let Some (IS.VStoreE _ _ ld rd _) = Seq.index i_st_ i_s in
                    related_in_store_tag e.l_child_in_store ld /\
                    related_in_store_tag e.r_child_in_store rd))
  = ()

let related_addm_parent_slots (a: addm_param)
                              (i_a: i_addm_param)
                              (st_: contents)
                              (i_st_: i_store)
  : Lemma (requires (related_addm_param a i_a /\ addm_precond a /\
                     addm_slot_postcond a st_ /\
                     IV.addm_slot_postcond i_a i_st_))
          (ensures (let s = addm_slot a in
                    let i_s = IV.addm_slot i_a in
                    let Some e = Seq.index st_ i_s in
                    let Some (IS.VStoreE _ _ _ _ p) = Seq.index i_st_ i_s in
                    related_parent_slot e.parent_slot p))
  = ()

let related_add_slot (a: addm_param)
                     (i_a: i_addm_param)
                     (tsm_: s_thread_state)
                     (i_tsm_: i_thread_state)
  : Lemma (requires (related_addm_param a i_a /\ addm_precond a /\
                     addm_postcond a tsm_ /\
                     IV.addm_postcond i_a i_tsm_))
          (ensures (let st_ = tsm_.store in
                    let i_st_ = i_tsm_.IV.st in
                    let i = IV.addm_slot i_a in
                    related_store_entry_opt (Seq.index st_ i) (Seq.index i_st_ i)))
  = let st_ = tsm_.store in
    let i_st_ = i_tsm_.IV.st in
    let s = addm_slot a in
    let i_s = IV.addm_slot i_a in

    assert (related_slot s i_s);
    assert (addm_slot_postcond a st_);
    assert (IV.addm_slot_postcond i_a i_st_);

    let Some e = Seq.index st_ i_s in
    assert (e.key = addm_key a);
    assert (addm_value_postcond a e.value);

    let Some (IS.VStoreE (i_gk, i_gv) i_am i_ld i_rd i_p)  = Seq.index i_st_ i_s in
    assert (i_gk = IV.addm_key i_a);
    assert (IV.addm_value_postcond i_a i_gv);

    related_addm_value a i_a e.value i_gv;
    assert (related_record (e.key, e.value) (i_gk, i_gv));
    assert (related_add_method e.add_method i_am);
    related_addm_slot_points a i_a st_ i_st_;
    related_addm_parent_slots a i_a st_ i_st_;
    ()

let related_anc_slot (a: addm_param)
                     (i_a: i_addm_param)
                     (tsm_: s_thread_state)
                     (i_tsm_: i_thread_state)
  : Lemma (requires (related_addm_param a i_a /\ addm_precond a /\
                     addm_postcond a tsm_ /\
                     IV.addm_postcond i_a i_tsm_))
          (ensures (let st_ = tsm_.store in
                    let i_st_ = i_tsm_.IV.st in
                    let i = IV.addm_anc_slot i_a in
                    related_store_entry_opt (Seq.index st_ i) (Seq.index i_st_ i)))
  = let st_ = tsm_.store in
    let st = addm_store_pre a in
    let i_st_ = i_tsm_.IV.st in
    let i_st = IV.addm_store_pre i_a in
    let s' = addm_anc_slot a in
    let i_s' = IV.addm_anc_slot i_a in

    assert (related_slot s' i_s');
    assert (related_store st i_st);

    (* the slot s' is related prior in pre-condition *)
    eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
    with i_s';

    let mv = addm_anc_val_pre a in
    let Some mv_ = to_merkle_value (stored_value st_ s') in
    assert (addm_anc_val_postcond a mv_);

    let i_mv = IV.addm_anc_val_pre i_a in
    let i_mv_ = R.to_merkle_value (IS.stored_value i_st_ i_s') in
    assert (IV.addm_anc_val_postcond i_a i_mv_);

    assert (related_mval mv i_mv);
    related_zero ();
    assert (related_mval mv_ i_mv_);
    ()

let related_desc_slot (a: addm_param)
                     (i_a: i_addm_param)
                     (tsm_: s_thread_state)
                     (i_tsm_: i_thread_state)
  : Lemma (requires (related_addm_param a i_a /\ addm_precond a /\
                     addm_postcond a tsm_ /\
                     IV.addm_postcond i_a i_tsm_ /\ IV.addm_has_desc_slot i_a))
          (ensures (let st_ = tsm_.store in
                    let i_st_ = i_tsm_.IV.st in
                    let i = IV.addm_desc_slot i_a in
                    related_store_entry_opt (Seq.index st_ i) (Seq.index i_st_ i)))
  = let st_ = tsm_.store in
    let st = addm_store_pre a in
    let i_st_ = i_tsm_.IV.st in
    let i_st = IV.addm_store_pre i_a in

    let sd = addm_desc_slot a in
    let i_sd = IV.addm_desc_slot i_a in

    assert (related_slot sd i_sd);
    assert (related_store st i_st);

    (* the slot s' is related prior in pre-condition *)
    eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
    with i_sd;

    ()

let addm_has_desc_slot_comp (a: addm_param {addm_precond a})
  : GTot bool
  = let mv' = addm_anc_val_pre a in
    let d = addm_dir a in
    let s' = addm_anc_slot a in
    let st' = addm_store_pre a in
    mv_points_to_some mv' d &&
    is_proper_descendent (mv_pointed_key mv' d) (addm_base_key a) &&
    SS.points_to_some_slot st' s' d

let related_unref_slot (a: addm_param)
                     (i_a: i_addm_param)
                     (tsm_: s_thread_state)
                     (i_tsm_: i_thread_state)
                     (i: i_slot_id)
  : Lemma (requires (related_addm_param a i_a /\ addm_precond a /\
                     addm_postcond a tsm_ /\
                     IV.addm_postcond i_a i_tsm_ /\
                     i <> IV.addm_slot i_a /\
                     i <> IV.addm_anc_slot i_a /\
                     (~ (IV.addm_has_desc_slot i_a) \/ i <> IV.addm_desc_slot i_a)))
          (ensures (let st_ = tsm_.store in
                    let i_st_ = i_tsm_.IV.st in
                    related_store_entry_opt (Seq.index st_ i) (Seq.index i_st_ i)))
  = let st_ = tsm_.store in
    let st = addm_store_pre a in
    let i_st_ = i_tsm_.IV.st in
    let i_st = IV.addm_store_pre i_a in
    let s = U16.uint_to_t i in

    (* the slot s' is related prior in pre-condition *)
    eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
    with i;

    if addm_has_desc_slot_comp a then
    begin
      assert (identical_except3 st_ st (addm_slot a) (addm_anc_slot a) (addm_desc_slot a));
      eliminate forall (s': T.slot).
      s' <> (addm_slot a) ==>
      s' <> (addm_anc_slot a) ==>
      s' <> (addm_desc_slot a) ==> get_slot st_ s' == get_slot st s'
      with s;


      eliminate forall (s': i_slot_id).
      s' <> (IV.addm_slot i_a) ==>
      s' <> (IV.addm_anc_slot i_a) ==>
      s' <> (IV.addm_desc_slot i_a) ==>
      IS.get_slot i_st_ s' = IS.get_slot i_st s'
      with i;

      ()
    end
    else
    begin

      eliminate forall (s': T.slot).
      s' <> (addm_slot a) ==>
      s' <> (addm_anc_slot a) ==>
      get_slot st_ s' == get_slot st s'
      with s;


      eliminate forall (s': i_slot_id).
      s' <> (IV.addm_slot i_a) ==>
      s' <> (IV.addm_anc_slot i_a) ==>
      IS.get_slot i_st_ s' = IS.get_slot i_st s'
      with i;

      ()
    end


let related_slot_addm_postcond (a: addm_param)
                               (i_a: i_addm_param)
                               (tsm_: s_thread_state)
                               (i_tsm_: i_thread_state)
                               (i: i_slot_id)
  : Lemma (requires (related_addm_param a i_a /\ addm_precond a /\
                     addm_postcond a tsm_ /\
                     IV.addm_postcond i_a i_tsm_))
          (ensures (let st_ = tsm_.store in
                    let i_st_ = i_tsm_.IV.st in
                    let e = Seq.index st_ i in
                    let i_e = Seq.index i_st_ i in
                    related_store_entry_opt e i_e))
  = if i = IV.addm_slot i_a then
      related_add_slot a i_a tsm_ i_tsm_
    else if i = IV.addm_anc_slot i_a then
      related_anc_slot a i_a tsm_ i_tsm_
    else if addm_has_desc_slot_comp a && i = IV.addm_desc_slot i_a then
      related_desc_slot a i_a tsm_ i_tsm_
    else
      related_unref_slot a i_a tsm_ i_tsm_ i

let related_store_addm_postcond (a: addm_param) (i_a: i_addm_param) (tsm_: s_thread_state) (i_tsm_: i_thread_state)
  : Lemma (requires (related_addm_param a i_a /\ addm_precond a /\
                     addm_postcond a tsm_ /\
                     IV.addm_postcond i_a i_tsm_))
          (ensures (related_store tsm_.store i_tsm_.IV.st))
  = let st_ = tsm_.store in
    let i_st_ = i_tsm_.IV.st in
    let aux (i:_)
      : Lemma (ensures (related_store_entry_opt (Seq.index st_ i) (Seq.index i_st_ i)))
      = related_slot_addm_postcond a i_a tsm_ i_tsm_ i
    in
    forall_intro aux

let related_addm_postcond (a: addm_param) (i_a: i_addm_param) (tsm_: s_thread_state) (i_tsm_: i_thread_state)
  : Lemma (requires (related_addm_param a i_a /\ addm_precond a /\
                     addm_postcond a tsm_ /\
                     IV.addm_postcond i_a i_tsm_))
          (ensures (related_tsm tsm_ i_tsm_))
  = let AMP s p s' tsm = a in
    let st = addm_store_pre a in
    let IV.AMP i_s (i_k, i_v) i_s' i_tsm = i_a in
    let i_st = IV.addm_store_pre i_a in

    assert (related_tsm tsm i_tsm);

    (* follows from the post condition *)
    assert (not tsm_.failed = i_tsm_.IV.valid);

    if not tsm_.failed then
      related_store_addm_postcond a i_a tsm_ i_tsm_
