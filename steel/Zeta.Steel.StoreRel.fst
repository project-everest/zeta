module Zeta.Steel.StoreRel

open FStar.Classical

module IS = Zeta.Intermediate.Store
module TSM = Zeta.Steel.ThreadStateModel

let lift_store (ss: s_store)
  : is: i_store { related_store ss is }
  = admit()

#push-options "--fuel 1 --ifuel 1 --query_stats"

let lemma_related_implies_parent_props (st: s_store) (i_st: i_store)
  : Lemma (requires (related_store st i_st))
          (ensures (parent_props st))
  = let aux (s:_)
      : Lemma (ensures (parent_props_local st s))
      = let i_s = U16.v s in
        eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
        with i_s;
        eliminate forall i. IS.parent_props_local i_st i
        with i_s;
        ()
    in
    forall_intro aux

let lemma_related_implies_points_to_inuse (st: s_store) (i_st: i_store)
  : Lemma (requires (related_store st i_st))
          (ensures (points_to_inuse st))
  = let aux (s1 s2:_)
      : Lemma (ensures (points_to_inuse_local st s1 s2))
      = let i_s1 = U16.v s1 in
        let i_s2 = U16.v s2 in
        eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
        with i_s1;
        eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
        with i_s2;
        eliminate forall i1 i2. IS.points_to_inuse_local i_st i_s1 i_s2
        with i_s1 i_s2;
        ()
    in
    forall_intro_2 aux

let lemma_related_implies_no_self_edges (st: s_store) (i_st: i_store)
  : Lemma (requires (related_store st i_st))
          (ensures (no_self_edges st))
  = let aux (s:_)
      : Lemma (ensures (no_self_edges_local st s))
      = let i_s = U16.v s in
        eliminate forall i. related_store_entry_opt (Seq.index st i) (Seq.index i_st i)
        with i_s;
        eliminate forall i. IS.no_self_edge_local i_st i
        with i_s;
        ()
    in
    forall_intro aux

#pop-options

let lemma_related_implies_all_props (st: s_store) (i_st: i_store)
  : Lemma (requires (related_store st i_st))
          (ensures (all_props st))
  = lemma_related_implies_parent_props st i_st;
    lemma_related_implies_points_to_inuse st i_st;
    lemma_related_implies_no_self_edges st i_st

let lemma_update_value (tsm: TSM.thread_state_model)
                       (s: T.slot {TSM.has_slot tsm s})
                       (v: T.value {T.is_value_of (TSM.key_of_slot tsm s) v})
  : Lemma (ensures (let tsm_ = TSM.update_value tsm s v in
                    identical_except_store tsm tsm_ /\
                    identical_except tsm.store tsm_.store s /\
                    inuse_slot tsm_.store s /\
                    (let Some e = get_slot tsm.store s in
                     let Some e_ = get_slot tsm_.store s in
                     e.key = e_.key /\ e_.value = v /\ e.add_method = e_.add_method /\
                     e.l_child_in_store = e_.l_child_in_store /\
                     e.r_child_in_store = e_.r_child_in_store)))
  = let tsm_ = TSM.update_value tsm s v in

    assert (identical_except_store tsm tsm_);
    assert (inuse_slot tsm_.store s);
    let aux (s':_)
      : Lemma (ensures (s' <> s ==> get_slot tsm.store s' == get_slot tsm_.store s'))
      = if s' <> s then ()
    in
    forall_intro aux;
    assert (identical_except tsm.store tsm_.store s);
    ()

let lemma_madd_to_store (tsm: TSM.thread_state_model)
                        (s: T.slot)
                        (k: T.key)
                        (v: T.value)
                        (s':T .slot)
                        (d: bool)
  : Lemma (requires (madd_to_store_reqs tsm s k v s' d))
          (ensures (let tsm_ = TSM.madd_to_store tsm s k v s' d in
                    let od = not d in
                    let open TSM in
                    identical_except_store tsm tsm_ /\
                    identical_except2 tsm.store tsm_.store s s' /\

                    // nothing changes in slot s' except it now points to s in direction d
                    inuse_slot tsm_.store s' /\
                    stored_key tsm_.store s' = stored_key tsm.store s' /\
                    stored_value tsm_.store s' = stored_value tsm.store s' /\
                    add_method_of tsm_.store s' = add_method_of tsm.store s' /\
                    points_to_dir tsm_.store s' d s /\
                    points_to_info tsm_.store s' od = points_to_info tsm.store s' od /\

                    // slot s contains (k, v, MAdd) and points to nothing
                    inuse_slot tsm_.store s /\
                    (let Some e = get_slot tsm_.store s in
                     e.key = k /\ e.value = v /\ e.add_method = MAdd /\
                     e.l_child_in_store = None /\ e.r_child_in_store = None /\
                     e.parent_slot = Some (s', d))))
  = let open TSM in
    let tsm_ = madd_to_store tsm s k v s' d in

    assert (identical_except_store tsm tsm_);
    let aux (s':_)
      : Lemma (ensures (s' <> s ==> s' <> s' ==> get_slot tsm.store s' == get_slot tsm_.store s'))
      = ()
    in
    forall_intro aux;
    ()

#push-options "--z3rlimit_factor 2 --query_stats"
let lemma_madd_to_store_split (tsm: TSM.thread_state_model)
                              (s: T.slot)
                              (k: T.key)
                              (v: T.value)
                              (s':T.slot)
                              (d d2:bool)
  : Lemma (requires (madd_to_store_split_reqs tsm s k v s' d d2 /\ all_props tsm.store))
          (ensures (let tsm_ = TSM.madd_to_store_split tsm s k v s' d d2 in
                    let od = not d in
                    let od2 = not d2 in
                    let s2 = pointed_slot tsm.store s' d in
                    let open TSM in

                    identical_except_store tsm tsm_ /\
                    identical_except3 tsm.store tsm_.store s s' s2 /\

                    // nothing changes in slot s', except it now points to s in direction d
                    inuse_slot tsm_.store s' /\
                    stored_key tsm_.store s' = stored_key tsm.store s' /\
                    stored_value tsm_.store s' = stored_value tsm.store s' /\
                    add_method_of tsm_.store s' = add_method_of tsm.store s' /\
                    points_to_dir tsm_.store s' d s /\
                    points_to_info tsm_.store s' od = points_to_info tsm.store s' od /\

                    // slot s contains (k, v, MAdd) and points to s2 along direction d2
                    inuse_slot tsm_.store s /\
                    stored_key tsm_.store s = k /\ stored_value tsm_.store s = v /\
                    add_method_of tsm_.store s = MAdd /\
                    points_to_none tsm_.store s od2 /\
                    points_to_dir tsm_.store s d2 s2 /\
                    has_parent tsm_.store s /\
                    parent_slot tsm_.store s = s' /\
                    parent_dir tsm_.store s = d /\

                    inuse_slot tsm_.store s2 /\ inuse_slot tsm.store s2 /\
                    has_parent tsm_.store s2 /\
                    parent_slot tsm_.store s2 = s /\
                    parent_dir tsm_.store s2 = d2 /\

                    (let Some e = get_slot tsm.store s2 in
                     let Some e_ = get_slot tsm_.store s2 in
                     e.key = e_.key /\ e.value = e_.value /\
                     e.add_method = e_.add_method /\
                     e.l_child_in_store = e_.l_child_in_store /\
                     e.r_child_in_store = e_.r_child_in_store)))
  = let tsm_ = TSM.madd_to_store_split tsm s k v s' d d2 in
    let od = not d in
    let od2 = not d2 in
    let s2 = pointed_slot tsm.store s' d in
    let open TSM in
    if tsm_.failed
    then admit()
    else (
    assert (tsm_.failed \/ identical_except_store tsm tsm_);
    assert (identical_except3 tsm.store tsm_.store s s' s2);

    assert (points_to_dir tsm.store s' d s2);
    eliminate forall (s1 s2: T.slot). points_to_inuse_local tsm.store s1 s2
    with s' s2;

    assert(inuse_slot tsm_.store s' /\
                    stored_key tsm_.store s' = stored_key tsm.store s' /\
                    stored_value tsm_.store s' = stored_value tsm.store s' /\
                    add_method_of tsm_.store s' = add_method_of tsm.store s' /\
                    points_to_dir tsm_.store s' d s /\
                    points_to_info tsm_.store s' od = points_to_info tsm.store s' od);
    assert(inuse_slot tsm_.store s /\
                    stored_key tsm_.store s = k /\ stored_value tsm_.store s = v /\
                    add_method_of tsm_.store s = MAdd /\
                    points_to_none tsm_.store s od2 /\
                    points_to_dir tsm_.store s d2 s2 /\
                    has_parent tsm_.store s /\
                    parent_slot tsm_.store s = s' /\
                    parent_dir tsm_.store s = d);
    assert(inuse_slot tsm_.store s2 /\ inuse_slot tsm.store s2);
    assert(has_parent tsm_.store s2);
    assert(parent_slot tsm_.store s2 = s);
    assert(parent_dir tsm_.store s2 = d2);
    assert (s <> s');
    assert (s <> s2);
    assert (s' <> s2);
    let st = tsm.store in
    match get_entry tsm s' with
    | Some r' ->
      let p = (s', d) in
      let s2_opt = child_slot r' d in
      assert (s2_opt = Some s2);
      //match s2_opt with
      //| None -> assert(False); ()
      //| Some s2 ->
        //if U16.v s2 >= Seq.length st
        //then
        //begin
          //assert(False); ()
        //end
        //else //match Seq.index st (U16.v s2) with
        //| None -> assert(False); ()
        //| Some r2 ->
                 //let e = mk_entry_full k v MAdd None None (Some p) in
                 //let e = update_child e d2 s2 in
                 //let e' = update_child r' d s in
                 //let p2new = s, d2 in
                 //let e2 = update_parent_slot r2 p2new in
          //assert(Some e2 == get_slot tsm_.store s2);
          //assert(Some r2 == get_slot tsm.store s2);
          //assert(e2.value = r2.value);


    (*
    assert(let Some e = get_slot tsm.store s2 in
           let Some e_ = get_slot tsm_.store s2 in
            e == r2 /\ e_ == e2 /\
           e.key = e_.key /\ e.add_method = e_.add_method /\
                     e.key = e_.key /\ e.value = e_.value /\
                     e.add_method = e_.add_method /\
                     e.l_child_in_store = e_.l_child_in_store /\
                     e.r_child_in_store = e_.r_child_in_store);
                    *)
    ()
  )
#pop-options

let lemma_mevict_from_store (tsm: s_thread_state)
                            (s: T.slot)
                            (s': T.slot)
                            (d: bool)
  : Lemma (requires (s <> s' /\ TSM.has_slot tsm s'))
          (ensures (let od = not d in
                    let st = tsm.store in
                    let open TSM in
                    let tsm_ = mevict_from_store tsm s s' d in
                    let st_ = tsm_.store in

                    // st and st_ are identical except at s, s'
                    identical_except2 st st_ s s' /\

                    // slot s is empty after update
                    empty_slot st_ s /\

                    // nothing changes in slot s', except it points to none in direction d
                    inuse_slot st_ s' /\
                    stored_key st_ s' = stored_key st s' /\
                    stored_value st_ s' = stored_value st s' /\
                    add_method_of st_ s' = add_method_of st s' /\
                    points_to_info st_ s' od = points_to_info st s' od /\
                    points_to_none st_ s' d /\
                    parent_info st_ s' = parent_info st s'))
  = let od = not d in
    let st = tsm.store in
    let open TSM in
    let tsm_ = mevict_from_store tsm s s' d in
    let st_ = tsm_.store in

    let aux (si:_)
      : Lemma (ensures (si <> s ==> si <> s' ==> get_slot st si == get_slot st_ si))
      = if si <> s && si <> s' then
           ()
    in
    forall_intro aux;
    assert (identical_except2 st st_ s s');

    assert (empty_slot st_ s);
    ()

let lemma_bevict_from_store (tsm: s_thread_state)
                            (s: T.slot)
  : Lemma (ensures (let st = tsm.store in
                    let open TSM in
                    let tsm_ = bevict_from_store tsm s in
                    let st_ = tsm_.store in
                    identical_except st st_ s /\
                    empty_slot st_ s))
  = let open TSM in
    let st = tsm.store in
    let tsm_ = bevict_from_store tsm s in
    let st_ = tsm_.store in

    let aux (s':_)
      : Lemma (ensures (s' <> s ==> get_slot st s' == get_slot st_ s'))
      = if s' <> s then ()
    in
    forall_intro aux;
    assert (identical_except st st_ s);

    ()
