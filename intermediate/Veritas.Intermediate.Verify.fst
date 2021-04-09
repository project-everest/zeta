module Veritas.Intermediate.Verify
open FStar.Classical

#push-options "--z3rlimit_factor 2"

let vaddm #vcfg (s:slot_id vcfg) (r:record) (s':slot_id vcfg) (vs: vtls vcfg {Valid? vs}):
  (vs': vtls vcfg {let a = AMP s r s' vs in
                   addm_precond a /\ addm_postcond a vs' \/
                   ~(addm_precond a) /\ Failed? vs'}) =
  let a = AMP s r s' vs in
  let st = thread_store vs in
  let (k,v) = r in
  if s = s' then Failed
  (* check slot s' is not empty *)
  else if empty_slot st s' then Failed
  else
    let k' = stored_key st s' in
    let v' = stored_value st s' in
    (* check k is a proper desc of k' *)
    if not (is_proper_desc k k') then Failed
    (* check slot s is empty *)
    else if inuse_slot st s then Failed
    (* check type of v is consistent with k *)
    else if not (is_value_of k v) then Failed
    else
      let v' = to_merkle_value v' in
      let d = desc_dir k k' in
      let dh' = desc_hash_dir v' d in
      let h = hashfn v in
      match dh' with
      | Empty -> (* k' has no child in direction d *)
        if v <> init_value k then Failed
        else if points_to_some_slot st s' d then Failed
        else
          let st_upd = madd_to_store st s k v s' d in
          let v'_upd = Spec.update_merkle_value v' d k h false in
          let st_upd = update_value st_upd s' (MVal v'_upd) in
          update_thread_store vs st_upd
      | Desc k2 h2 b2 ->
        if k2 = k then (* k is a child of k' *)
          if not (h2 = h && b2 = false) then Failed
          (* check slot s' does not contain a desc along direction d *)
          else if points_to_some_slot st s' d then Failed
          else
            let st_upd = madd_to_store st s k v s' d in
            update_thread_store vs st_upd
        else (* otherwise, k is not a child of k' *)
          (* first add must be init value *)
          if v <> init_value k then Failed
          (* check k2 is a proper desc of k *)
          else if not (is_proper_desc k2 k) then Failed
          else
            let d2 = desc_dir k2 k in
            let mv = to_merkle_value v in
            let mv_upd = Spec.update_merkle_value mv d2 k2 h2 b2 in
            let v'_upd = Spec.update_merkle_value v' d k h false in
            let st_upd =  if points_to_some_slot st s' d then
                            madd_to_store_split st s k (MVal mv_upd) s' d d2
                          else
                            madd_to_store st s k (MVal mv_upd) s' d in
            let st_upd = update_value st_upd s' (MVal v'_upd) in
            update_thread_store vs st_upd

#pop-options

let lemma_verify_failed (#vcfg:_) (vs:vtls vcfg) (e:_)
  : Lemma (requires (Failed? vs))
          (ensures (Failed? (verify_step vs e)))
  = ()

let rec lemma_verifiable_implies_prefix_verifiable_aux
      (#vcfg:_)
      (vsinit: vtls vcfg)
      (l: logS _{verifiable vsinit l})
      (i: seq_index l):
  Lemma (ensures (let li = prefix l i in
                  verifiable vsinit li))
        (decreases (Seq.length l)) =
  let n = Seq.length l in
  if n = 0 then ()
  else if i = n - 1 then()
  else
    lemma_verifiable_implies_prefix_verifiable_aux vsinit (prefix l (n - 1)) i

let rec lemma_verifiable_implies_init_valid_aux #vcfg (vsinit: vtls vcfg) (l: logS _):
  Lemma (requires (verifiable vsinit l))
        (ensures (Valid? vsinit))
        (decreases (Seq.length l)) =
  let n = Seq.length l in
  if n = 0 then ()
  else (
    let l' = prefix l (n - 1) in
    lemma_verifiable_implies_prefix_verifiable_aux vsinit l (n - 1);
    lemma_verifiable_implies_init_valid_aux vsinit l'
  )

let lemma_verifiable_implies_init_valid (#vcfg:_) (vsinit: vtls vcfg) (l: logS _):
  Lemma (requires (verifiable vsinit l))
        (ensures (Valid? vsinit))
  = lemma_verifiable_implies_init_valid_aux vsinit l

let lemma_verifiable_implies_prefix_verifiable
      (#vcfg:_)
      (vsinit: vtls vcfg)
      (l: logS _{verifiable vsinit l})
      (i: seq_index l):
  Lemma (ensures (let li = prefix l i in
                  verifiable vsinit li))
  = lemma_verifiable_implies_prefix_verifiable_aux vsinit l i

let lemma_addm_props (#vcfg:_)
                     (vs:vtls vcfg{Valid? vs})
                     (e:logS_entry _{AddM_S? e}):
  Lemma (requires (Valid? (verify_step vs e)))
        (ensures (let AddM_S s (k,v) s' = e in
                  let st' = thread_store vs in
                  inuse_slot st' s' /\
                  (let k' = stored_key st' s' in
                   is_proper_desc k k' /\
                   is_merkle_key k' /\
                   (let mv' = to_merkle_value (stored_value st' s') in
                    let d = desc_dir k k' in
                    (mv_points_to_none mv' d ||
                     is_desc (mv_pointed_key mv' d) k))))) =
  let AddM_S s (k, v) s' = e in
  let st' = thread_store vs in
  // assert(inuse_slot st s');

  let k' = stored_key st' s' in
  assert(is_proper_desc k k');
  assert(is_merkle_key k');
  let mv' = to_merkle_value (stored_value st' s') in
  let d = desc_dir k k' in
  let dh' = desc_hash_dir mv' d in
  match dh' with
  | Empty -> ()
  | Desc k2 _ _  ->
    if k2 = k then lemma_desc_reflexive k
    else ()

let lemma_addm_identical_except2 #vcfg (vs':vtls vcfg{Valid? vs'}) (e: logS_entry _ {AddM_S? e}) s1:
  Lemma (requires (let AddM_S s (k,v) s' = e in
                  s1 <> s /\ s1 <> s' /\
                  Valid? (verify_step vs' e)))
        (ensures (let st' = thread_store vs' in
                  let vs = verify_step vs' e in
                  let st = thread_store vs in
                  empty_slot st' s1 = empty_slot st s1 /\            // empty-ness unchanged
                  (inuse_slot st' s1 ==>
                   stored_key st' s1 = stored_key st s1 /\
                   stored_value st' s1 = stored_value st s1 /\
                   add_method_of st' s1 = add_method_of st s1))) =
  match e with
  | AddM_S s (k,v) s' ->
    let amp = AMP s (k,v) s' vs' in
    let vs = verify_step vs' e in

    (* precond is satisfied since verify_step succeeds *)
    assert(addm_precond amp);

    let st' = addm_store_pre amp in
    let st = thread_store vs in
    let d = addm_dir amp in
    let mv' = addm_anc_val_pre amp in

    if mv_points_to_some mv' d then (
      if mv_points_to mv' d k then (
        assert(identical_except2 st' st s s');
        assert(get_slot st' s1 = get_slot st s1);
        ()
      )
      else (
        assert(addm_anc_points_to_desc amp);
        if points_to_some_slot st' s' d then  (
          assert(addm_has_desc_slot amp);
          let sd = addm_desc_slot amp in
          assert(identical_except3 st' st s s' sd);
          if sd = s1 then (
            ()
          )
          else
            assert(get_slot st' s1 = get_slot st s1)
        )
        else (
          assert(identical_except2 st' st s s');
          assert(get_slot st' s1 = get_slot st s1);
          ()
        )
      )
    )
    else (
      assert(identical_except2 st' st s s');
      assert(get_slot st' s1 = get_slot st s1);
      ()
    )

let lemma_addm_propsC #vcfg (vs':vtls vcfg{Valid? vs'}) (e: logS_entry _ {AddM_S? e}):
  Lemma (requires (Valid? (verify_step vs' e)))
        (ensures (let st' = thread_store vs' in
                  let vs = verify_step vs' e in
                  let st = thread_store vs in
                  let AddM_S s (k,v) s' = e in
                  inuse_slot st' s' /\
                  inuse_slot st s' /\
                  stored_key st' s' = stored_key st s')) =
   ()

let lemma_evictm_props #vcfg (vs':vtls vcfg{Valid? vs'}) (e: logS_entry _ {EvictM_S? e}):
  Lemma (requires (Valid? (verify_step vs' e)))
        (ensures (let st' = thread_store vs' in
                  let vs = verify_step vs' e in
                  let st = thread_store vs in
                  let EvictM_S s s' = e in
                  inuse_slot st' s /\ inuse_slot st' s' /\
                  empty_slot st s /\ inuse_slot st s' /\
                  stored_key st s' = stored_key st' s' /\
                  identical_except2 st st' s s')) =  ()

let lemma_evictbm_props #vcfg (vs':vtls vcfg{Valid? vs'}) (e: logS_entry _ {EvictBM_S? e}):
  Lemma (requires (Valid? (verify_step vs' e)))
        (ensures (let st' = thread_store vs' in
                  let vs = verify_step vs' e in
                  let st = thread_store vs in
                  let EvictBM_S s s' _ = e in
                  inuse_slot st' s /\ inuse_slot st' s' /\
                  empty_slot st s /\ inuse_slot st s' /\
                  stored_key st s' = stored_key st' s' /\
                  identical_except2 st st' s s')) = ()

let lemma_init_consistent_log #vcfg (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l}):
  Lemma (requires (Seq.length l = 0))
        (ensures (let st = thread_store vsinit in
                  let s2kinit = to_slot_state_map st in
                  consistent_log s2kinit l /\
                  (let stend = thread_store (verify vsinit l) in
                   let s2kend = S.to_slot_state_map stend in
                   let s2klog = L.to_slot_state_map s2kinit l in
                   FE.feq s2kend s2klog))) =
  let stinit = thread_store vsinit in
  let s2kinit = to_slot_state_map stinit in
  let stend = thread_store (verify vsinit l) in
  let s2kend = S.to_slot_state_map stend in

  let aux (s:slot_id vcfg):
      Lemma (ensures (slot_state_trans_closure s l (s2kinit s) <> None))
            [SMTPat (slot_state_trans_closure s l (s2kinit s))] =
      ()
  in
  assert(consistent_log s2kinit l);
  assert(stend == stinit);
  let s2klog = L.to_slot_state_map s2kinit l in

  let aux (s:slot_id vcfg):
    Lemma (ensures (s2kend s == s2klog s))
          [SMTPat (s2kend s == s2klog s)] =
    // assert(s2kend s == (if inuse_slot stinit s then Assoc (stored_key stinit s) else Free));
    ()
  in
  // assert(FE.feq s2kend s2klog);
  ()

let lemma_verifiable_implies_consistent_log_feq_get #vcfg (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l /\ Seq.length l > 0}):
  Lemma (requires (let n = Seq.length l in
                   let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let l' = prefix l (n - 1) in
                   let st' = thread_store (verify vsinit l') in
                   let s2k' = S.to_slot_state_map st' in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let e = Seq.index l (n - 1) in
                   Get_S? e /\
                   consistent_log s2kinit l' /\
                   consistent_log s2kinit l /\
                   (let s2klog' = L.to_slot_state_map s2kinit l' in
                    FE.feq s2k' s2klog')))
         (ensures (let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let s2klog = L.to_slot_state_map s2kinit l in
                   FE.feq s2k s2klog)) =
  let stinit = thread_store vsinit in
  let s2kinit = to_slot_state_map stinit in
  let vs = verify vsinit l in
  let st = thread_store vs in
  let s2k = S.to_slot_state_map st in
  let s2klog = L.to_slot_state_map s2kinit l in

  let n = Seq.length l in
  let e = Seq.index l (n - 1) in

  let l' = prefix l (n - 1) in
  let s2klog' = Logs.to_slot_state_map s2kinit l' in
  let vs' = verify vsinit l' in
  let st' = thread_store vs' in
  let s2k' = S.to_slot_state_map st' in

  match e with
  | Get_S s1 k1 v1 ->
    let aux2 (s:slot_id vcfg):
      Lemma (ensures (s2k s == s2klog s)) =
      let ss0 = s2kinit s in
      let ss' = slot_state_trans_closure s l' ss0 in
      assert(ss' <> None);

      let ss = slot_state_trans_closure s l ss0 in
      assert(ss == slot_state_trans e s (Some?.v ss'));
      assert(s2klog s = Some?.v ss);
      assert(s2k' s = s2klog' s);

      if s1 = s then (
        assert(inuse_slot st' s);
        assert(stored_key st' s = stored_key st s);
        assert(s2k' s = s2k s);
        assert(s2klog' s = s2klog s);
        ()
      )
      else (
        assert(s2klog' s = s2klog s);
        assert(vs == vget s1 k1 v1 vs');
        assert(identical_except st st' s1);
          assert(get_slot st s = get_slot st' s);
          assert(inuse_slot st s = inuse_slot st' s);

          if inuse_slot st s then (
            assert(stored_key st s = stored_key st' s);
            assert(s2k s = s2k' s);
            ()
          )
          else ()
      )
    in
    forall_intro aux2;
    assert(FE.feq s2k s2klog);
    ()

let lemma_verifiable_implies_consistent_log_feq_put #vcfg (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l /\ Seq.length l > 0}):
  Lemma (requires (let n = Seq.length l in
                   let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let l' = prefix l (n - 1) in
                   let st' = thread_store (verify vsinit l') in
                   let s2k' = S.to_slot_state_map st' in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let e = Seq.index l (n - 1) in
                   Put_S? e /\
                   consistent_log s2kinit l' /\
                   consistent_log s2kinit l /\
                   (let s2klog' = L.to_slot_state_map s2kinit l' in
                    FE.feq s2k' s2klog')))
         (ensures (let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let s2klog = L.to_slot_state_map s2kinit l in
                   FE.feq s2k s2klog)) =
  let stinit = thread_store vsinit in
  let s2kinit = to_slot_state_map stinit in
  let vs = verify vsinit l in
  let st = thread_store vs in
  let s2k = S.to_slot_state_map st in
  let s2klog = L.to_slot_state_map s2kinit l in

  let n = Seq.length l in
  let e = Seq.index l (n - 1) in

  let l' = prefix l (n - 1) in
  let s2klog' = Logs.to_slot_state_map s2kinit l' in
  let vs' = verify vsinit l' in
  let st' = thread_store vs' in
  let s2k' = S.to_slot_state_map st' in

  match e with
  | Put_S s1 k1 v1 ->
    let aux2 (s:slot_id vcfg):
      Lemma (ensures (s2k s == s2klog s)) =
      let ss0 = s2kinit s in
      let ss' = slot_state_trans_closure s l' ss0 in
      assert(ss' <> None);

      let ss = slot_state_trans_closure s l ss0 in
      assert(ss == slot_state_trans e s (Some?.v ss'));
      assert(s2klog s = Some?.v ss);
      assert(s2k' s = s2klog' s);

      if s1 = s then (
        assert(inuse_slot st' s);
        assert(stored_key st' s = stored_key st s);
        assert(s2k' s = s2k s);
        assert(s2klog' s = s2klog s);
        ()
      )
      else (
        assert(s2klog' s = s2klog s);
        assert(vs == vput s1 k1 v1 vs');
        assert(identical_except st st' s1);
          assert(get_slot st s = get_slot st' s);
          assert(inuse_slot st s = inuse_slot st' s);

          if inuse_slot st s then (
            assert(stored_key st s = stored_key st' s);
            assert(s2k s = s2k' s);
            ()
          )
          else ()
      )
    in
    forall_intro aux2;
    assert(FE.feq s2k s2klog);
    ()

#push-options "--query_stats --z3rlimit_factor 4"
let lemma_verifiable_implies_consistent_log_feq_addm #vcfg (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l /\ Seq.length l > 0}):
  Lemma (requires (let n = Seq.length l in
                   let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let l' = prefix l (n - 1) in
                   let st' = thread_store (verify vsinit l') in
                   let s2k' = S.to_slot_state_map st' in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let e = Seq.index l (n - 1) in
                   AddM_S? e /\
                   consistent_log s2kinit l' /\
                   consistent_log s2kinit l /\
                   (let s2klog' = L.to_slot_state_map s2kinit l' in
                    FE.feq s2k' s2klog')))
         (ensures (let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let s2klog = L.to_slot_state_map s2kinit l in
                   FE.feq s2k s2klog)) =
  let stinit = thread_store vsinit in
  let s2kinit = to_slot_state_map stinit in
  let vs = verify vsinit l in
  let st = thread_store vs in
  let s2k = S.to_slot_state_map st in
  let s2klog = L.to_slot_state_map s2kinit l in

  let n = Seq.length l in
  let e = Seq.index l (n - 1) in

  let l' = prefix l (n - 1) in
  let s2klog' = Logs.to_slot_state_map s2kinit l' in
  let vs' = verify vsinit l' in
  let st' = thread_store vs' in
  let s2k' = S.to_slot_state_map st' in

  match e with
  | AddM_S s1 (k1,_) s2 ->
    let aux (s:slot_id vcfg):
      Lemma (ensures (s2k s == s2klog s)) =
      let ss0 = s2kinit s in
      let ss' = slot_state_trans_closure s l' ss0 in
      assert(ss' <> None);

      let ss = slot_state_trans_closure s l ss0 in
      assert(ss == slot_state_trans e s (Some?.v ss'));
      assert(s2klog s = Some?.v ss);
      assert(s2k' s = s2klog' s);

      if s1 = s then (
        assert(s2klog s = Assoc k1);
        assert(s2k s = Assoc k1);
        ()
      )
      else if s2 = s then (
        assert(inuse_slot st' s);
        assert(ss = ss');
        assert(s2klog s = s2klog' s);
        lemma_addm_propsC vs' e;
        assert(s2k s = s2k' s);
        ()
      )
      else (
        assert(ss = ss');
        assert(s2klog s = s2klog' s);
        lemma_addm_identical_except2 vs' e s;
        //assert(identical_except2 st st' s1 s2);
        //assert(get_slot st s = get_slot st' s);
        assert(s2k s = s2k' s);
        ()
      )
    in
    forall_intro aux;
    assert(FE.feq s2k s2klog);
    ()
#pop-options

let lemma_verifiable_implies_consistent_log_feq_addb #vcfg (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l /\ Seq.length l > 0}):
  Lemma (requires (let n = Seq.length l in
                   let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let l' = prefix l (n - 1) in
                   let st' = thread_store (verify vsinit l') in
                   let s2k' = S.to_slot_state_map st' in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let e = Seq.index l (n - 1) in
                   AddB_S? e /\
                   consistent_log s2kinit l' /\
                   consistent_log s2kinit l /\
                   (let s2klog' = L.to_slot_state_map s2kinit l' in
                    FE.feq s2k' s2klog')))
         (ensures (let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let s2klog = L.to_slot_state_map s2kinit l in
                   FE.feq s2k s2klog)) =
  let stinit = thread_store vsinit in
  let s2kinit = to_slot_state_map stinit in
  let vs = verify vsinit l in
  let st = thread_store vs in
  let s2k = S.to_slot_state_map st in
  let s2klog = L.to_slot_state_map s2kinit l in

  let n = Seq.length l in
  let e = Seq.index l (n - 1) in

  let l' = prefix l (n - 1) in
  let s2klog' = Logs.to_slot_state_map s2kinit l' in
  let vs' = verify vsinit l' in
  let st' = thread_store vs' in
  let s2k' = S.to_slot_state_map st' in

  match e with
  | AddB_S s1 (k1,_) _ _ ->
    let aux (s:slot_id vcfg):
      Lemma (ensures (s2k s == s2klog s)) =
      let ss0 = s2kinit s in
      let ss' = slot_state_trans_closure s l' ss0 in
      assert(ss' <> None);

      let ss = slot_state_trans_closure s l ss0 in
      assert(ss == slot_state_trans e s (Some?.v ss'));
      assert(s2klog s = Some?.v ss);
      assert(s2k' s = s2klog' s);
      if s1 = s then (
        assert(s2klog s = Assoc k1);
        assert(s2k s = Assoc k1);
        ()
      )
      else (
        assert(ss' = ss);
        assert(s2klog s = s2klog' s);
        assert(s2k s = s2k' s);
        ()
      )
    in
    forall_intro aux;
    assert(FE.feq s2k s2klog);
    ()

let lemma_verifiable_implies_consistent_log_feq_evictm #vcfg (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l /\ Seq.length l > 0}):
  Lemma (requires (let n = Seq.length l in
                   let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let l' = prefix l (n - 1) in
                   let st' = thread_store (verify vsinit l') in
                   let s2k' = S.to_slot_state_map st' in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let e = Seq.index l (n - 1) in
                   EvictM_S? e /\
                   consistent_log s2kinit l' /\
                   consistent_log s2kinit l /\
                   (let s2klog' = L.to_slot_state_map s2kinit l' in
                    FE.feq s2k' s2klog')))
         (ensures (let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let s2klog = L.to_slot_state_map s2kinit l in
                   FE.feq s2k s2klog)) =
  let stinit = thread_store vsinit in
  let s2kinit = to_slot_state_map stinit in
  let vs = verify vsinit l in
  let st = thread_store vs in
  let s2k = S.to_slot_state_map st in
  let s2klog = L.to_slot_state_map s2kinit l in

  let n = Seq.length l in
  let e = Seq.index l (n - 1) in

  let l' = prefix l (n - 1) in
  let s2klog' = Logs.to_slot_state_map s2kinit l' in
  let vs' = verify vsinit l' in
  let st' = thread_store vs' in
  let s2k' = S.to_slot_state_map st' in
  match e with
  | EvictM_S s1 s2 ->
    let aux (s:slot_id vcfg):
      Lemma (ensures (s2k s == s2klog s)) =
      let ss0 = s2kinit s in
      let ss' = slot_state_trans_closure s l' ss0 in
      assert(ss' <> None);

      let ss = slot_state_trans_closure s l ss0 in
      assert(ss == slot_state_trans e s (Some?.v ss'));
      assert(s2klog s = Some?.v ss);
      assert(s2k' s = s2klog' s);
      lemma_evictm_props vs' e;

      if s1 = s then (
        assert(empty_slot st s);
        assert(s2k s = Free);
        assert(s2klog s = Free);
        ()
      )
      else if s2 = s then (
        assert(s2klog s = s2klog' s);
        assert(s2k s = s2k' s);
        ()
      )
      else (
        assert(ss = ss');
        assert(s2klog s = s2klog' s);
        assert(identical_except2 st st' s1 s2);
        assert(get_slot st s = get_slot st' s);
        assert(s2k s = s2k' s);
        ()
      )
    in
    forall_intro aux;
    assert(FE.feq s2k s2klog);
    ()

let lemma_verifiable_implies_consistent_log_feq_evictb #vcfg (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l /\ Seq.length l > 0}):
  Lemma (requires (let n = Seq.length l in
                   let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let l' = prefix l (n - 1) in
                   let st' = thread_store (verify vsinit l') in
                   let s2k' = S.to_slot_state_map st' in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let e = Seq.index l (n - 1) in
                   EvictB_S? e /\
                   consistent_log s2kinit l' /\
                   consistent_log s2kinit l /\
                   (let s2klog' = L.to_slot_state_map s2kinit l' in
                    FE.feq s2k' s2klog')))
         (ensures (let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let s2klog = L.to_slot_state_map s2kinit l in
                   FE.feq s2k s2klog)) =
  let stinit = thread_store vsinit in
  let s2kinit = to_slot_state_map stinit in
  let vs = verify vsinit l in
  let st = thread_store vs in
  let s2k = S.to_slot_state_map st in
  let s2klog = L.to_slot_state_map s2kinit l in

  let n = Seq.length l in
  let e = Seq.index l (n - 1) in

  let l' = prefix l (n - 1) in
  let s2klog' = Logs.to_slot_state_map s2kinit l' in
  let vs' = verify vsinit l' in
  let st' = thread_store vs' in
  let s2k' = S.to_slot_state_map st' in

  match e with
  | EvictB_S s1 _ ->
    let aux (s:slot_id vcfg):
      Lemma (ensures (s2k s == s2klog s)) =
      let ss0 = s2kinit s in
      let ss' = slot_state_trans_closure s l' ss0 in
      assert(ss' <> None);

      let ss = slot_state_trans_closure s l ss0 in
      assert(ss == slot_state_trans e s (Some?.v ss'));
      assert(s2klog s = Some?.v ss);
      assert(s2k' s = s2klog' s);

      if s1 = s then (
        assert(empty_slot st s);
        assert(s2k s = Free);
        assert(s2klog s = Free);
        ()
      )
      else (
        assert(ss = ss');
        assert(s2klog s = s2klog' s);
        assert(identical_except st st' s1);
        assert(s2k s = s2k' s);
        ()
      )
    in
    forall_intro aux;
    assert(FE.feq s2k s2klog);
    ()

let lemma_verifiable_implies_consistent_log_feq_evictbm #vcfg (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l /\ Seq.length l > 0}):
  Lemma (requires (let n = Seq.length l in
                   let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let l' = prefix l (n - 1) in
                   let st' = thread_store (verify vsinit l') in
                   let s2k' = S.to_slot_state_map st' in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let e = Seq.index l (n - 1) in
                   EvictBM_S? e /\
                   consistent_log s2kinit l' /\
                   consistent_log s2kinit l /\
                   (let s2klog' = L.to_slot_state_map s2kinit l' in
                    FE.feq s2k' s2klog')))
         (ensures (let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let s2klog = L.to_slot_state_map s2kinit l in
                   FE.feq s2k s2klog)) =
  let stinit = thread_store vsinit in
  let s2kinit = to_slot_state_map stinit in
  let vs = verify vsinit l in
  let st = thread_store vs in
  let s2k = S.to_slot_state_map st in
  let s2klog = L.to_slot_state_map s2kinit l in

  let n = Seq.length l in
  let e = Seq.index l (n - 1) in

  let l' = prefix l (n - 1) in
  let s2klog' = Logs.to_slot_state_map s2kinit l' in
  let vs' = verify vsinit l' in
  let st' = thread_store vs' in
  let s2k' = S.to_slot_state_map st' in
  lemma_evictbm_props vs' e;

  match e with
  | EvictBM_S s1 s2 _ ->
    let aux (s:slot_id vcfg):
      Lemma (ensures (s2k s == s2klog s)) =
      let ss0 = s2kinit s in
      let ss' = slot_state_trans_closure s l' ss0 in
      assert(ss' <> None);

      let ss = slot_state_trans_closure s l ss0 in
      assert(ss == slot_state_trans e s (Some?.v ss'));
      assert(s2klog s = Some?.v ss);
      assert(s2k' s = s2klog' s);
      if s1 = s then (
        assert(empty_slot st s);
        assert(s2k s = Free);
        assert(s2klog s = Free);
        ()
      )
      else if s2 = s then (
        assert(s2klog s = s2klog' s);
        assert(s2k s = s2k' s);
        ()
      )
      else (
        assert(ss = ss');
        assert(s2klog s = s2klog' s);
        assert(identical_except2 st st' s1 s2);
        assert(get_slot st s = get_slot st' s);
        assert(s2k s = s2k' s);
        ()
      )
    in
    forall_intro aux;
    assert(FE.feq s2k s2klog);
    ()

let lemma_verifiable_implies_consistent_log_feq #vcfg (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l /\ Seq.length l > 0}):
  Lemma (requires (let n = Seq.length l in
                   let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let l' = prefix l (n - 1) in
                   let st' = thread_store (verify vsinit l') in
                   let s2k' = S.to_slot_state_map st' in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   consistent_log s2kinit l' /\
                   consistent_log s2kinit l /\
                   (let s2klog' = L.to_slot_state_map s2kinit l' in
                    FE.feq s2k' s2klog')))
         (ensures (let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let st = thread_store (verify vsinit l) in
                   let s2k = S.to_slot_state_map st in
                   let s2klog = L.to_slot_state_map s2kinit l in
                   FE.feq s2k s2klog)) =
  let n = Seq.length l in
  let e = Seq.index l (n - 1) in
  match e with
  | Get_S _ _ _ -> lemma_verifiable_implies_consistent_log_feq_get vsinit l
  | Put_S _ _ _ -> lemma_verifiable_implies_consistent_log_feq_put vsinit l
  | AddM_S _ _ _ -> lemma_verifiable_implies_consistent_log_feq_addm vsinit l
  | EvictM_S _ _ -> lemma_verifiable_implies_consistent_log_feq_evictm vsinit l
  | AddB_S _ _ _ _ -> lemma_verifiable_implies_consistent_log_feq_addb vsinit l
  | EvictB_S _ _ -> lemma_verifiable_implies_consistent_log_feq_evictb vsinit l
  | EvictBM_S _ _ _ -> lemma_verifiable_implies_consistent_log_feq_evictbm vsinit l

let lemma_verifiable_implies_consistent_extend #vcfg (vsinit: vtls vcfg) (l: logS _{Seq.length l > 0 /\ verifiable vsinit l}):
  Lemma (requires (let n = Seq.length l in
                   let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                   let l' = prefix l (n - 1) in
                   consistent_log s2kinit l' /\
                   (let st' = thread_store (verify vsinit l') in
                    let s2k' = S.to_slot_state_map st' in
                    let s2klog' = L.to_slot_state_map s2kinit l' in
                    FE.feq s2k' s2klog')))
         (ensures (let stinit = thread_store vsinit in
                   let s2kinit = to_slot_state_map stinit in
                  consistent_log s2kinit l)) =
  let stinit = thread_store vsinit in
  let s2kinit = to_slot_state_map stinit in
  let vs = verify vsinit l in
  let st = thread_store vs in
  let s2k = S.to_slot_state_map st in
  let n = Seq.length l in
  let l' = prefix l (n - 1) in
  let e = Seq.index l (n - 1) in
  let s2klog' = Logs.to_slot_state_map s2kinit l' in
  let vs' = verify vsinit l' in
  let st' = thread_store vs' in
  let s2k' = S.to_slot_state_map st' in

  let aux (s: slot_id vcfg):
    Lemma (ensures (slot_state_trans_closure s l (s2kinit s) <> None))
          [SMTPat (slot_state_trans_closure s l (s2kinit s))] =
    let ss0 = s2kinit s in
    let ss' = slot_state_trans_closure s l' ss0 in
    assert(ss' <> None);

    let ss = slot_state_trans_closure s l ss0 in
    assert(ss == slot_state_trans e s (Some?.v ss'));
    match e with
    | Get_S s1 k1 _ ->
      if s1 = s then (
         assert(inuse_slot st' s1);
         assert(stored_key st' s1 = k1);
         assert(s2k' s1 = Assoc k1);
         ()
      )
      else ()
    | Put_S s1 k1 _ ->
      if s1 = s then (
         assert(inuse_slot st' s1);
         assert(stored_key st' s1 = k1);
         assert(s2k' s1 = Assoc k1);
         ()
      )
      else ()
    | AddM_S s1 (k1,v1) s2 ->
      if s1 = s then (
         assert(empty_slot st' s1);
         assert(s2k' s1 = Free);
         ()
      )
      else if s2 = s then (
        assert(inuse_slot st' s);
        assert(Assoc? (s2k' s));
        ()
      )
      else ()
    | AddB_S s1 (k1,_) _ _ ->
      if s1 = s then (
         assert(empty_slot st' s);
         assert(s2k' s = Free);
         ()
      )
      else ()
    | EvictM_S s1 s2 ->
      assert(inuse_slot st' s1);
      assert(inuse_slot st' s2);
      assert(Assoc? (s2k' s1));
      assert(Assoc? (s2k' s2));
      ()
    | EvictB_S s1 _ ->
      assert(inuse_slot st' s1);
      assert(Assoc? (s2k' s1));
      ()

    | EvictBM_S s1 s2 _ ->
      assert(inuse_slot st' s1);
      assert(inuse_slot st' s2);
      assert(Assoc? (s2k' s1));
      assert(Assoc? (s2k' s2));
      ()
  in
  assert(consistent_log s2kinit l);
  ()

let rec lemma_verifiable_implies_consistent_log_aux (#vcfg:_) (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l}):
  Lemma (ensures (let st = thread_store vsinit in
                  let s2kinit = to_slot_state_map st in
                  consistent_log s2kinit l /\
                  (let stend = thread_store (verify vsinit l) in
                   let s2kend = S.to_slot_state_map stend in
                   let s2klog = L.to_slot_state_map s2kinit l in
                   FE.feq s2kend s2klog)))
        (decreases (Seq.length l)) =
  let stinit = thread_store vsinit in
  let s2kinit = to_slot_state_map stinit in
  let vs = verify vsinit l in
  let st = thread_store vs in
  let s2k = S.to_slot_state_map st in
  let n = Seq.length l in
  if n = 0 then
     lemma_init_consistent_log vsinit l
  else (
    let l' = prefix l (n - 1) in
    let e = Seq.index l (n - 1) in
    lemma_verifiable_implies_consistent_log_aux vsinit l';
    assert(consistent_log s2kinit l');
    lemma_verifiable_implies_consistent_extend vsinit l;
    assert(consistent_log s2kinit l);
    lemma_verifiable_implies_consistent_log_feq vsinit l
  )

(* verifiability implies consistency of the log *)
let lemma_verifiable_implies_consistent_log (#vcfg:_) (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l}):
  Lemma (ensures (let st = thread_store vsinit in
                  let s2k = to_slot_state_map st in
                  consistent_log s2k l))
  = lemma_verifiable_implies_consistent_log_aux vsinit l

(* the association of slot -> keys in store is what is mandated by the log *)
let lemma_s2k_store_eq_s2k_log (#vcfg:_) (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l}):
  Lemma (ensures (let stinit = thread_store vsinit in
                  let s2kinit = S.to_slot_state_map stinit in
                  let stend = thread_store (verify vsinit l) in
                  let s2kend = S.to_slot_state_map stend in
                  let s2klog = L.to_slot_state_map s2kinit l in
                  FE.feq s2kend s2klog))
   = lemma_verifiable_implies_consistent_log_aux vsinit l

let lemma_verifiable_implies_slot_is_merkle_points_to_get (#vcfg:_)
                                                      (vs:vtls vcfg)
                                                      (e: logS_entry _{Get_S? e}):
  Lemma (requires (Valid? vs /\ slot_points_to_is_merkle_points_to (thread_store vs) /\
                   Valid? (verify_step vs e)))
        (ensures (slot_points_to_is_merkle_points_to (thread_store (verify_step vs e)))) =
  ()

let lemma_verifiable_implies_slot_is_merkle_points_to_put (#vcfg:_)
                                                      (vs:vtls vcfg)
                                                      (e: logS_entry _{Put_S? e}):
  Lemma (requires (Valid? vs /\ slot_points_to_is_merkle_points_to (thread_store vs) /\
                   Valid? (verify_step vs e)))
        (ensures (slot_points_to_is_merkle_points_to (thread_store (verify_step vs e)))) =
  let st = thread_store vs in
  let vs1 = verify_step vs e in
  let st1 = thread_store vs1 in

  let aux (s1 s2: slot_id _) (d: bin_tree_dir):
    Lemma (slot_points_to_is_merkle_points_to_local st1 s1 s2 d) =
    assert(slot_points_to_is_merkle_points_to_local st s1 s2 d);
    ()
  in
  forall_intro_3 aux;
  ()

#push-options "--max_fuel 1 --max_ifuel 0 --z3rlimit_factor 2"

let lemma_verifiable_implies_slot_is_merkle_points_to_addm (#vcfg:_)
                                                      (vs:vtls vcfg)
                                                      (e: logS_entry _{AddM_S? e}):
  Lemma (requires (Valid? vs /\ slot_points_to_is_merkle_points_to (thread_store vs) /\
                   Valid? (verify_step vs e)))
        (ensures (slot_points_to_is_merkle_points_to (thread_store (verify_step vs e)))) =
  let vs1 = verify_step vs e in
  let st1 = thread_store vs1 in

  //lemma_addm_propsB vs e;
  match e with
  | AddM_S s r s' ->
    let a = AMP s r s' vs in
    let st = thread_store vs in

    //assert(identical_except2 st st1 s' s);
    assert(vs1 == vaddm s r s' vs);

    let aux (s1 s2: slot_id _) (dx: bin_tree_dir):
      Lemma (slot_points_to_is_merkle_points_to_local st1 s1 s2 dx) =
      assert(slot_points_to_is_merkle_points_to_local st s1 s2 dx);

      if not (points_to_dir st1 s1 dx s2) then ()
      else if s1 = s then (
         assert(points_to_dir st s' (addm_dir a) s2);
         assert(slot_points_to_is_merkle_points_to_local st (addm_anc_slot a) s2 (addm_dir a));
         assert(s2 <> s);
         assert(s2 <> s');
         lemma_addm_identical_except2 vs e s2
      )
      else if s1 = s' then (
        if s2 = s then (
          let mv1' = to_merkle_value (stored_value st1 s') in
          let d = addm_dir a in
          assert(addm_anc_val_postcond a mv1');

          if d = dx then ()
          else (
            // let mv' = to_merkle_value (stored_value st s') in
            // assert(desc_hash_dir mv1' dx = desc_hash_dir mv' dx);
            assert(addm_anc_slot_points_postcond a st1);
            assert(points_to_info st1 s' dx = points_to_info st s' dx);
            assert(points_to_dir st1 s' dx s2);
            assert(points_to_dir st s' dx s2);
            ()
          )
        )
        else (
          assert(s2 <> s);
          if s2 = s' then (
            assert(slot_points_to_is_merkle_points_to_local st s' s' dx);
            ()
          )
          else (
            assert(get_slot st s2 = get_slot st1 s2);
            assert(addm_anc_slot_points_postcond a st1);
            assert(dx = other_dir (addm_dir a));
            assert(s1 = addm_anc_slot a);
            assert(points_to_info st1 s' dx = points_to_info st s' dx);
            assert(points_to_dir st s' dx s2);
            assert(stored_key st s' = stored_key st1 s');
            ()
          )
        )
      )
      else
        lemma_addm_identical_except2 vs e s1
    in
    forall_intro_3 aux;
    ()

#pop-options

let lemma_verifiable_implies_slot_is_merkle_points_to_evictm (#vcfg:_)
                                                      (vs:vtls vcfg)
                                                      (e: logS_entry _{EvictM_S? e}):
  Lemma (requires (Valid? vs /\ slot_points_to_is_merkle_points_to (thread_store vs) /\
                   Valid? (verify_step vs e)))
        (ensures (slot_points_to_is_merkle_points_to (thread_store (verify_step vs e)))) =
  let vs1 = verify_step vs e in
  let st1 = thread_store vs1 in
  let st = thread_store vs in
  match e with
  | EvictM_S s s' ->
    assert(empty_slot st1 s);
    assert(identical_except2 st st1 s s');
    let k = stored_key st s in
    let k' = stored_key st s' in
    assert(is_proper_desc k k');
    let d = desc_dir k k' in

    let aux (s1 s2: slot_id _) (dx: bin_tree_dir):
      Lemma (slot_points_to_is_merkle_points_to_local st1 s1 s2 dx) =

      if not (points_to_dir st1 s1 dx s2) then ()
      else (
        assert(s1 <> s);

        if s1 = s' then (
          assert(dx = other_dir d);
          assert(points_to_info st s' dx = points_to_info st1 s' dx);
          ()
        )
        else (
          assert(get_slot st s1 = get_slot st1 s1);
          assert(points_to_dir st s1 dx s2);
          assert(slot_points_to_is_merkle_points_to_local st s1 s2 dx);
          ()
        )
      )
    in
    forall_intro_3 aux;
    ()

let lemma_verifiable_implies_slot_is_merkle_points_to_addb (#vcfg:_)
                                                      (vs:vtls vcfg)
                                                      (e: logS_entry _{AddB_S? e}):
  Lemma (requires (Valid? vs /\ slot_points_to_is_merkle_points_to (thread_store vs) /\
                   Valid? (verify_step vs e)))
        (ensures (slot_points_to_is_merkle_points_to (thread_store (verify_step vs e)))) =
  let vs1 = verify_step vs e in
  let st1 = thread_store vs1 in
  let st = thread_store vs in

  match e with
  | AddB_S s (k,v) _ _  ->
    let aux (s1 s2: slot_id _) (dx: bin_tree_dir):
      Lemma (slot_points_to_is_merkle_points_to_local st1 s1 s2 dx) =
      if not (points_to_dir st1 s1 dx s2) then ()
      else (
        (* s points to nothing after addb *)
        assert(s1 <> s);
        assert(get_slot st s1 = get_slot st1 s1);
        assert(slot_points_to_is_merkle_points_to_local st s1 s2 dx);
        assert(points_to_dir st s1 dx s2);
        ()
      )
    in
    forall_intro_3 aux;
    ()

let lemma_verifiable_implies_slot_is_merkle_points_to_evictb (#vcfg:_)
                                                      (vs:vtls vcfg)
                                                      (e: logS_entry _{EvictB_S? e}):
  Lemma (requires (Valid? vs /\ slot_points_to_is_merkle_points_to (thread_store vs) /\
                   Valid? (verify_step vs e)))
        (ensures (slot_points_to_is_merkle_points_to (thread_store (verify_step vs e)))) =
  let vs1 = verify_step vs e in
  let st1 = thread_store vs1 in
  let st = thread_store vs in

  match e with
  | EvictB_S s  _  ->
    let aux (s1 s2: slot_id _) (dx: bin_tree_dir):
      Lemma (slot_points_to_is_merkle_points_to_local st1 s1 s2 dx) =

      if not (points_to_dir st1 s1 dx s2) then ()
      else (
        assert(s <> s1);
        assert(get_slot st s1 = get_slot st1 s1);
        assert(slot_points_to_is_merkle_points_to_local st s1 s2 dx);
        assert(points_to_dir st s1 dx s2);
        ()
      )
    in
    forall_intro_3 aux


#push-options "--z3rlimit_factor 2"

let lemma_verifiable_implies_slot_is_merkle_points_to_evictbm (#vcfg:_)
                                                      (vs:vtls vcfg)
                                                      (e: logS_entry _{EvictBM_S? e}):
  Lemma (requires (Valid? vs /\ slot_points_to_is_merkle_points_to (thread_store vs) /\
                   Valid? (verify_step vs e)))
        (ensures (slot_points_to_is_merkle_points_to (thread_store (verify_step vs e)))) =

  let vs1 = verify_step vs e in
  let st1 = thread_store vs1 in
  let st = thread_store vs in

  match e with
  | EvictBM_S s s'  _  ->
    assert(identical_except2 st1 st s s');
    let k = stored_key st s in
    let k' = stored_key st s' in
    assert(is_proper_desc k k');
    let d = desc_dir k k' in

    let aux (s1 s2: slot_id _) (dx: bin_tree_dir):
      Lemma (slot_points_to_is_merkle_points_to_local st1 s1 s2 dx) =

      if not (points_to_dir st1 s1 dx s2) then ()
      else (
        assert(s <> s1);
        if s1 = s' then (
          assert(dx = other_dir d);
          assert(points_to_info st s' dx = points_to_info st1 s' dx);
          assert(slot_points_to_is_merkle_points_to_local st s1 s2 dx);
          ()
        )
        else (
          assert(get_slot st s1 = get_slot st1 s1);
          assert(slot_points_to_is_merkle_points_to_local st s1 s2 dx);
          assert(points_to_dir st s1 dx s2);
          ()
        )
      )
    in
    forall_intro_3 aux

#pop-options

(* if there are no verification failures, slot_points to implies merkle points to property is
 * propagates *)
let lemma_verifiable_implies_slot_is_merkle_points_to (#vcfg:_)
                                                      (vs:vtls vcfg)
                                                      (e: logS_entry _):
  Lemma (requires (Valid? vs /\ slot_points_to_is_merkle_points_to (thread_store vs) /\
                   Valid? (verify_step vs e)))
        (ensures (slot_points_to_is_merkle_points_to (thread_store (verify_step vs e)))) =
  match e with
  | Get_S s k v -> lemma_verifiable_implies_slot_is_merkle_points_to_get vs e
  | Put_S _ _ _ -> lemma_verifiable_implies_slot_is_merkle_points_to_put vs e
  | AddM_S _ _ _ -> lemma_verifiable_implies_slot_is_merkle_points_to_addm vs e
  | EvictM_S _ _ -> lemma_verifiable_implies_slot_is_merkle_points_to_evictm vs e
  | AddB_S _ _ _ _ -> lemma_verifiable_implies_slot_is_merkle_points_to_addb vs e
  | EvictB_S _ _ -> lemma_verifiable_implies_slot_is_merkle_points_to_evictb vs e
  | EvictBM_S _ _ _ -> lemma_verifiable_implies_slot_is_merkle_points_to_evictbm vs e

let lemma_vget_simulates_spec
      (#vcfg:_)
      (vss:vtls vcfg{Valid? vss})
      (vsk:Spec.vtls)
      (e:logS_entry vcfg{Get_S? e})
  : Lemma (requires (vtls_rel vss vsk /\
                     valid_logS_entry vss e))
          (ensures (let ek = to_logK_entry vss e in
                    vtls_rel (verify_step vss e) (Spec.t_verify_step vsk ek))) = ()

let lemma_vget_preserves_ismap
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (e:logS_entry _{Get_S? e})
  : Lemma (requires (S.is_map (thread_store vs)))
          (ensures (Valid? (verify_step vs e) ==> S.is_map (thread_store (verify_step vs e))))
  = ()

let lemma_vput_preserves_ismap
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (e:logS_entry _{Put_S? e})
  : Lemma (requires (S.is_map (thread_store vs)))
          (ensures (Valid? (verify_step vs e) ==> S.is_map (thread_store (verify_step vs e))))
  = ()

let lemma_vput_simulates_spec
      (#vcfg:_)
      (vss:vtls vcfg{Valid? vss})
      (vsk:Spec.vtls)
      (e:logS_entry vcfg{Put_S? e})
  : Lemma (requires (vtls_rel vss vsk /\
                     valid_logS_entry vss e))
          (ensures (let ek = to_logK_entry vss e in
                    vtls_rel (verify_step vss e) (Spec.t_verify_step vsk ek))) =
   let sts = thread_store vss in
   let sts_map = as_map sts in
   let stk = Spec.thread_store vsk in

   match e with
   | Put_S s k v ->

     let ek = to_logK_entry vss e in
     assert(ek = Spec.Put k v);

     let vss1 = verify_step vss e in
     let vsk1 = Spec.t_verify_step vsk ek in

     (* otherwise valid_logS_entry e would be false *)
     assert(not (empty_slot sts s) /\ stored_key sts s = k);

     (* no more reason for the put operation to fail *)
     assert(Valid? vss1 /\ Spec.Valid? vsk1);

     let sts1 = thread_store vss1 in
     let sts1_map = as_map sts1 in
     let stk1 = Spec.thread_store vsk1 in

     let aux (kx: key)
       : Lemma (ensures (stk1 kx = sts1_map kx))
               [SMTPat (stk1 kx)] =
       if store_contains_key sts kx then (
         if kx = k then (
           // assert(stored_key sts1 s = kx);
           ()
         )
         else (
           let sx = slot_of_key sts kx in
           assert(get_slot sts1 sx = get_slot sts sx);
           ()
         )
       )
       else
         if Spec.store_contains sts1_map kx then (
           let sx = slot_of_key sts1 kx in
           // assert(sx <> s);
           assert(get_slot sts1 sx = get_slot sts sx);
           ()
         )
         else ()
     in
     // assert(FE.feq sts1_map stk1)
     ()

(* if the key is not present in store and store is a map, then store remains a map after add *)
let lemma_vaddm_preserves_ismap_new_key
      (#vcfg:_)
      (vs':vtls vcfg{Valid? vs'})
      (e:logS_entry _{AddM_S? e})
  : Lemma (requires (let st' = thread_store vs' in
                     let AddM_S _ (k,_) _ = e in
                     is_map st' /\ not (store_contains_key st' k)))
          (ensures (Valid? (verify_step vs' e) ==> S.is_map (thread_store (verify_step vs' e)))) = ()

let lemma_vaddm_preserves_spec_unrelatedkey #vcfg
  (vss: vtls vcfg {Valid? vss})
  (vsk: Spec.vtls)
  (e: logS_entry _ {AddM_S? e})
  (k2: key)
  : Lemma (requires (let sts = thread_store vss in
                     let AddM_S _ (k,_) s' = e in
                     vtls_rel vss vsk /\
                     valid_logS_entry vss e /\
                     not (store_contains_key sts k) /\
                     Valid? (verify_step vss e) /\
                     Spec.Valid? (Spec.t_verify_step vsk (to_logK_entry vss e)) /\
                     k2 <> k /\
                     k2 <> stored_key sts s'))
          (ensures (let ek = to_logK_entry vss e in
                    let vss1 = verify_step vss e in
                    let sts1 = thread_store vss1 in
                    let vsk1 = Spec.t_verify_step vsk ek in
                    let stk1 = Spec.thread_store vsk1 in
                    lemma_vaddm_preserves_ismap_new_key vss e;
                    let sts1_map = as_map sts1 in
                    stk1 k2 = sts1_map k2)) =
  let sts = thread_store vss in
  let sts_map = as_map sts in
  let stk = Spec.thread_store vsk in
  let s2k = S.to_slot_state_map sts in
  let ek = to_logK_entry vss e in

  match e with
  | AddM_S s (k,v) s' ->
    let a = AMP s (k,v) s' vss in
    (* otherwise e would not be a valid log entry *)
    assert(inuse_slot sts s');
    let k' = stored_key sts s' in
    assert(ek = Spec.AddM (k,v) k');

    assert(Spec.store_contains stk k');
    assert(Spec.stored_value stk k' = stored_value sts s');

    assert(is_proper_desc k k');
    let d = desc_dir k k' in

    let vss1 = verify_step vss e in
    let sts1 = thread_store vss1 in
    lemma_vaddm_preserves_ismap_new_key vss e;
    let sts1_map = as_map sts1 in
    let vsk1 = Spec.t_verify_step vsk ek in
    let stk1 = Spec.thread_store vsk1 in

    (* precond - k2 is an unrelated key *)
    assert(k2 <> k /\ k2 <> k');
    (* k2 is in the store prior to add *)
    if Spec.store_contains stk k2 then (
      assert(Spec.store_contains sts_map k2);

      (* let s2 be the slot that contains k2 *)

      let s2 = slot_of_key sts k2 in
      assert(stored_key sts s2 = k2);

      (* this implies s2 is neither s or s' since they contain different keys *)
      assert(s2 <> s && s2 <> s');

      (* since all slots except s and s' are unchanged, s2 remains unchanged by the addm *)
      lemma_addm_identical_except2 vss e s2;

      //assert(get_slot sts s2 = get_slot sts1 s2);
      assert(stored_key sts1 s2 = k2);
      assert(stored_value sts1 s2 = stored_value sts s2);

      lemma_as_map_slot_key_equiv sts1 s2;
      assert(Spec.store_contains sts1_map k2);
      assert(Spec.store_contains stk1 k2);

      ()
    )
    else (
      assert(not (Spec.store_contains sts_map k2));
      assert(not (store_contains_key sts k2));
      assert(not (Spec.store_contains stk k2));

      (* and we have sufficient info to prove that k2 is not in spec store after the addm *)
      assert(not (Spec.store_contains stk1 k2));

      if Spec.store_contains sts1_map k2 then (
        let s2 = slot_of_key sts1 k2 in
        assert(s2 <> s && s2 <> s');

        assert(get_slot sts s2 = get_slot sts1 s2);
        ()
      )
      else ()
    )

let lemma_vaddm_preserves_spec_key #vcfg
  (vss: vtls vcfg {Valid? vss})
  (vsk: Spec.vtls)
  (e: logS_entry _ {AddM_S? e})
  : Lemma (requires (let sts = thread_store vss in
                     let AddM_S _ (k,_) s' = e in
                     vtls_rel vss vsk /\
                     valid_logS_entry vss e /\
                     not (store_contains_key sts k) /\
                     Valid? (verify_step vss e) /\
                     Spec.Valid? (Spec.t_verify_step vsk (to_logK_entry vss e))))
          (ensures (let ek = to_logK_entry vss e in
                    let vss1 = verify_step vss e in
                    let sts1 = thread_store vss1 in
                    let vsk1 = Spec.t_verify_step vsk ek in
                    let stk1 = Spec.thread_store vsk1 in
                    let AddM_S _ (k,_) s' = e in
                    lemma_vaddm_preserves_ismap_new_key vss e;
                    let sts1_map = as_map sts1 in
                    stk1 k = sts1_map k)) =
  let sts = thread_store vss in
  let sts_map = as_map sts in
  let stk = Spec.thread_store vsk in
  let s2k = S.to_slot_state_map sts in
  let ek = to_logK_entry vss e in

  match e with
  | AddM_S s (k,v) s' ->
    let a = AMP s (k,v) s' vss in
    (* otherwise e would not be a valid log entry *)
    assert(inuse_slot sts s');
    let k' = stored_key sts s' in
    assert(ek = Spec.AddM (k,v) k');

    assert(Spec.store_contains stk k');
    assert(Spec.stored_value stk k' = stored_value sts s');

    assert(is_proper_desc k k');
    let d = desc_dir k k' in

    let vss1 = verify_step vss e in
    let sts1 = thread_store vss1 in
    lemma_vaddm_preserves_ismap_new_key vss e;
    let sts1_map = as_map sts1 in
    let vsk1 = Spec.t_verify_step vsk ek in
    let stk1 = Spec.thread_store vsk1 in

    assert(stored_key sts1 s = k);
    let v = stored_value sts1 s in
    assert(v = Spec.stored_value sts1_map k);
    ()

let lemma_vaddm_preserves_spec_anc_key #vcfg
  (vss: vtls vcfg {Valid? vss})
  (vsk: Spec.vtls)
  (e: logS_entry _ {AddM_S? e})
  : Lemma (requires (let sts = thread_store vss in
                     let AddM_S _ (k,_) s' = e in
                     vtls_rel vss vsk /\
                     valid_logS_entry vss e /\
                     not (store_contains_key sts k) /\
                     Valid? (verify_step vss e) /\
                     Spec.Valid? (Spec.t_verify_step vsk (to_logK_entry vss e))))
          (ensures (let sts = thread_store vss in
                    let ek = to_logK_entry vss e in
                    let vss1 = verify_step vss e in
                    let sts1 = thread_store vss1 in
                    let vsk1 = Spec.t_verify_step vsk ek in
                    let stk1 = Spec.thread_store vsk1 in
                    let AddM_S _ _ s' = e in
                    let k' = stored_key sts s' in
                    lemma_vaddm_preserves_ismap_new_key vss e;
                    let sts1_map = as_map sts1 in
                    stk1 k' = sts1_map k')) = ()

let lemma_vaddm_preserves_spec_new_key_caseValid
      (#vcfg:_)
      (vss:vtls vcfg{Valid? vss})
      (vsk:Spec.vtls)
      (e:logS_entry _{AddM_S? e})
  : Lemma (requires (let sts = thread_store vss in
                     let AddM_S _ (k,_) _ = e in
                     vtls_rel vss vsk /\
                     valid_logS_entry vss e /\
                     not (store_contains_key sts k) /\
                     slot_points_to_is_merkle_points_to sts) /\
                     Valid? (verify_step vss e))
          (ensures (let ek = to_logK_entry vss e in
                    vtls_rel (verify_step vss e) (Spec.t_verify_step vsk ek))) =
  let sts = thread_store vss in
  let stk = Spec.thread_store vsk in
  let s2k = S.to_slot_state_map sts in
  let ek = to_logK_entry vss e in

  match e with
  | AddM_S s (k,v) s' ->

    let a = AMP s (k,v) s' vss in
    (* otherwise e would not be a valid log entry *)
    assert(inuse_slot sts s');
    let k' = stored_key sts s' in
    assert(ek = Spec.AddM (k,v) k');

    assert(Spec.store_contains stk k');
    assert(Spec.stored_value stk k' = stored_value sts s');

    assert(is_proper_desc k k');
    let d = desc_dir k k' in

    let vss1 = verify_step vss e in
    let vsk1 = Spec.t_verify_step vsk ek in

    assert(thread_clock vss1 = Spec.thread_clock vsk1);
    assert(thread_hadd vss1 = Spec.thread_hadd vsk1);
    assert(thread_hevict vss1 = Spec.thread_hevict vsk1);
    assert(Valid?.id vss1 = Spec.Valid?.id vsk1);

    let sts1 = thread_store vss1 in
    lemma_vaddm_preserves_ismap_new_key vss e;
    assert(is_map sts1);
    let sts1_map = as_map sts1 in
    let stk1 = Spec.thread_store vsk1 in

    let aux (k2: key):
      Lemma (ensures (sts1_map k2 == stk1 k2)) =
      if k2 = k then lemma_vaddm_preserves_spec_key vss vsk e
      else if k2 = k' then lemma_vaddm_preserves_spec_anc_key vss vsk e
      else lemma_vaddm_preserves_spec_unrelatedkey vss vsk e k2
    in
    forall_intro aux;
    assert(FE.feq stk1 sts1_map);
    ()

(* adding a key not in store to vaddm preserves the spec relationship *)
let lemma_vaddm_preserves_spec_new_key
      (#vcfg:_)
      (vss:vtls vcfg{Valid? vss})
      (vsk:Spec.vtls)
      (e:logS_entry _{AddM_S? e})
  : Lemma (requires (let sts = thread_store vss in
                     let AddM_S _ (k,_) _ = e in
                     vtls_rel vss vsk /\
                     valid_logS_entry vss e /\
                     not (store_contains_key sts k) /\
                     slot_points_to_is_merkle_points_to sts))
          (ensures (let ek = to_logK_entry vss e in
                    vtls_rel (verify_step vss e) (Spec.t_verify_step vsk ek))) =
  let sts = thread_store vss in
  let stk = Spec.thread_store vsk in
  let s2k = S.to_slot_state_map sts in
  let ek = to_logK_entry vss e in
  match e with
  | AddM_S s (k,v) s' ->

    let a = AMP s (k,v) s' vss in
    (* otherwise e would not be a valid log entry *)
    assert(inuse_slot sts s');
    let k' = stored_key sts s' in
    assert(ek = Spec.AddM (k,v) k');

    let vss1 = verify_step vss e in
    let vsk1 = Spec.t_verify_step vsk ek in

    if Valid? vss1 then
      lemma_vaddm_preserves_spec_new_key_caseValid vss vsk e
    else (
      (* some precondition was not satisfied to cause the failure *)
      assert(~(addm_precond a));

      (* otherwise e would not be a valid log entry *)
      assert(empty_slot sts s);

      (* spec would fail as well *)
      if not (is_value_of k v) then ()

      (* spec would fail *)
      else if not (is_proper_desc k k') then ()

      else (

        assert(addm_precond1 a);

        (* ancestor merkle value in intermediate *)
        let mvs' = addm_anc_val_pre a in
        let d = addm_dir a in

        (* and it should be the same in spec *)
        assert(Spec.stored_value stk k' = MVal mvs');

        if mv_points_to_none mvs' d then (
          assert(addm_precond2 a /\ addm_anc_points_null a);

          (* since a does not satisfy precond, one of these should hold *)
          assert(v <> init_value k \/
                 points_to_some_slot sts s' (addm_dir a));

          (* spec fails as well *)
          if v <> init_value k then ()

          else (
            (* intermediate fails because s' points to some slot along addm direction *)
            assert(points_to_some_slot sts s' (addm_dir a));

            let s2 = pointed_slot sts s' (addm_dir a) in
            assert(slot_points_to_is_merkle_points_to_local sts s' s2 (addm_dir a));

            (* which produces a contradiction since we have mv_points_none mvs' d *)
            assert(False);
            ()
          )
        )
        else if mv_points_to mvs' d k then (
          assert(addm_precond2 a /\ addm_anc_points_to_key a);

          assert(desc_hash_dir mvs' d <> Desc k (hashfn v) false \/
                 points_to_some_slot sts s' d);

          if desc_hash_dir mvs' d <> Desc k (hashfn v) false then ()
          else (
            (* if s' points to a slot s2, then from our invariant, s2 should contain key k
             * which produces a contradiction since we assumed k is not in the store *)
            let s2 = pointed_slot sts s' d in

            assert(slot_points_to_is_merkle_points_to_local sts s' s2 d);
            assert(stored_key sts s2 = k);

            ()
          )
        )
        else if is_proper_desc (mv_pointed_key mvs' d) k then (
          assert(addm_precond2 a /\ addm_anc_points_to_desc a);

          assert(addm_value_pre a <> init_value (addm_key a));

          ()
        )
        else ()
      )
    )

(* if the key is not present in store and store is a map, then store remains a map after add *)
let lemma_vaddb_preserves_ismap_new_key
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (e:logS_entry _{AddB_S? e})
  : Lemma (requires (let st = thread_store vs in
                     let AddB_S _ (k,_) _ _ = e in
                     is_map st /\ not (store_contains_key st k)))
          (ensures (Valid? (verify_step vs e) ==> S.is_map (thread_store (verify_step vs e))))
  = ()

(* addb preserves spec relationship if the kew is not in store *)
let lemma_vaddb_preserves_spec_new_key
      (#vcfg:_)
      (vss:vtls vcfg{Valid? vss})
      (vsk:Spec.vtls)
      (e:logS_entry _{AddB_S? e})
  : Lemma (requires (let st = thread_store vss in
                     let AddB_S _ (k,_) _ _ = e in
                     vtls_rel vss vsk /\
                     valid_logS_entry vss e /\
                     not (store_contains_key st k)))
          (ensures (let ek = to_logK_entry vss e in
                    vtls_rel (verify_step vss e) (Spec.t_verify_step vsk ek))) =
  let sts = thread_store vss in
  let sts_map = as_map sts in
  let stk = Spec.thread_store vsk in

  match e with
  | AddB_S s (k,v) t j ->

    let ek = to_logK_entry vss e in
    assert(ek = Spec.AddB (k,v) t j);

    assert(empty_slot sts s);

    (* incompatible value - both spec and int will fail *)
    if not (is_value_of k v) then ()

    else
      let vss1 = verify_step vss e in
      let sts1 = thread_store vss1 in
      let _ = lemma_vaddb_preserves_ismap_new_key vss e in
      let sts1_map = as_map sts1 in

      let vsk1 = Spec.t_verify_step vsk ek in
      let stk1 = Spec.thread_store vsk1 in

      let aux (k2: key):
        Lemma (ensures (sts1_map k2 = stk1 k2)) =
        if k2 = k then ()
        else if Spec.store_contains stk1 k2 then (
          assert(stk1 k2 = stk k2);
          assert(stk k2 = sts_map k2);

          let s2 = slot_of_key sts k2 in
          assert(s2 <> s);
          assert(get_slot sts s2 = get_slot sts1 s2);

          ()
        )
        else if Spec.store_contains sts1_map k2 then (
          let s2 = slot_of_key sts1 k2 in
          assert(get_slot sts s2 = get_slot sts1 s2);
          assert(inuse_slot sts s2);
          assert(sts1_map k2 = sts_map k2);
          ()
        )
        else ()
      in
      forall_intro aux

let lemma_evictb_preserves_ismap
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (e:logS_entry _{EvictB_S? e})
  : Lemma (requires (S.is_map (thread_store vs)))
          (ensures (Valid? (verify_step vs e) ==> S.is_map (thread_store (verify_step vs e))))
  = ()

let lemma_points_to_some_implies_has_instore_merkle_desc
  (#vcfg:_)
  (sts: vstore vcfg)
  (stk: Spec.vstore)
  (s: inuse_slot_id sts)
  : Lemma (requires (store_rel sts stk /\
                     slot_points_to_is_merkle_points_to sts /\
                     merkle_points_to_uniq sts /\
                     merkle_points_to_desc sts /\
                     (points_to_some_slot sts s Left || points_to_some_slot sts s Right)))
          (ensures (let k = stored_key sts s in
                    Spec.has_instore_merkle_desc stk k)) =
  let k = stored_key sts s in
  let d = if points_to_some_slot sts s Left then Left else Right in
  let sd = pointed_slot sts s d in
  assert(slot_points_to_is_merkle_points_to_local sts s sd d);
  assert(points_to_dir sts s d sd);
  assert(inuse_slot sts sd);

  let mv = to_merkle_value (stored_value sts s) in
  let kd = stored_key sts sd in
  assert(mv_points_to mv d kd);
  assert(Spec.store_contains stk kd);
  assert(mv = to_merkle_value (Spec.stored_value stk k));
  assert(add_method_of sts sd = Spec.MAdd);
  ()

let lemma_has_instore_merkle_desc_implies_slot_points_to
  (#vcfg:_)
  (sts: vstore vcfg)
  (stk: Spec.vstore)
  (s: inuse_slot_id sts)
  : Lemma (requires (let k = stored_key sts s in
                     store_rel sts stk /\
                     slot_points_to_is_merkle_points_to sts /\
                     merkle_points_to_uniq sts /\
                     merkle_points_to_desc sts /\
                     Spec.store_contains stk k /\
                     Spec.has_instore_merkle_desc stk k))
          (ensures (points_to_some_slot sts s Left || points_to_some_slot sts s Right )) =
  let k = stored_key sts s in
  assert(Spec.has_instore_merkle_desc stk k);
  assert(is_merkle_key k);
  let mv = to_merkle_value (Spec.stored_value stk k) in
  assert(mv = to_merkle_value (stored_value sts s));
  let ld = desc_hash_dir mv Left in
  let rd = desc_hash_dir mv Right in

  assert(Desc? ld && Spec.is_instore_madd stk (Desc?.k ld) ||
    Desc? rd && Spec.is_instore_madd stk (Desc?.k rd));

  let d = if Desc? ld && Spec.is_instore_madd stk (Desc?.k ld) then Left else Right in
  let kd = mv_pointed_key mv d in

  assert(Spec.store_contains stk kd /\ Spec.add_method_of stk kd = Spec.MAdd);
  let sd = slot_of_key sts kd in
  assert(stored_key sts sd = kd /\ add_method_of sts sd = Spec.MAdd);
  assert(merkle_points_to_desc_local sts s d);

  assert(kd <> Root);
  let s2 = pointing_slot sts sd in
  assert(points_to sts s2 sd);

  let d2 = if points_to_dir sts s2 Left sd then Left else Right in
  assert(points_to_dir sts s2 d2 sd);
  assert(slot_points_to_is_merkle_points_to_local sts s2 sd d2);
  let mv2 = to_merkle_value (stored_value sts s2) in

  assert(mv_points_to mv2 d2 kd);
  assert(mv_points_to mv d kd);

  if s2 = s then ()
  else (
    assert(merkle_points_to_uniq_local sts s s2 kd);
    ()
  )

let lemma_evictb_simulates_spec
      (#vcfg:_)
      (vss:vtls vcfg{Valid? vss})
      (vsk:Spec.vtls)
      (e:logS_entry vcfg{EvictB_S? e})
  : Lemma (requires (let sts = thread_store vss in
                     vtls_rel vss vsk /\
                     valid_logS_entry vss e /\
                     slot_points_to_is_merkle_points_to sts /\
                     merkle_points_to_uniq sts /\
                     merkle_points_to_desc sts))
          (ensures (let ek = to_logK_entry vss e in
                    vtls_rel (verify_step vss e) (Spec.t_verify_step vsk ek))) =
  let sts = thread_store vss in
  let sts_map = as_map sts in
  let stk = Spec.thread_store vsk in

  match e with
  | EvictB_S s t ->

    assert(inuse_slot sts s);
    let k = stored_key sts s in
    let ek = to_logK_entry vss e in
    assert(ek = Spec.EvictB k t);
    let clk = Valid?.clock vss in

    if k = Root then ()
    else if not (clk `ts_lt` t) then ()
    else if points_to_some_slot sts s Left || points_to_some_slot sts s Right then
      lemma_points_to_some_implies_has_instore_merkle_desc sts stk s
    else
      let vss1 = verify_step vss e in
      let vsk1 = Spec.t_verify_step vsk ek in
      if add_method_of sts s <> Spec.BAdd then ()
      else (
        assert(Valid? vss1);
        assert(ts_lt (Spec.Valid?.clk vsk) t);
        assert(Spec.store_contains stk k);
        assert(Spec.add_method_of stk k = Spec.BAdd);

        if Spec.has_instore_merkle_desc stk k then
          lemma_has_instore_merkle_desc_implies_slot_points_to sts stk s
        else (
          assert(Spec.Valid? vsk1);
          let sts1 = thread_store vss1  in
          let sts1_map = as_map sts1 in
          let stk1 = Spec.thread_store vsk1 in
          let aux (k2: key):
            Lemma (ensures (sts1_map k2 = stk1 k2)) =
            if k2 = k then lemma_not_contains_after_bevict sts s
            else if Spec.store_contains stk1 k2 then (
              assert(stk1 k2 = stk k2);
              let s2 = slot_of_key sts k2 in
              assert(s2 <> s);
              assert(get_slot sts s2 = get_slot sts1 s2);
              assert(stored_key sts1 s2 = k2);
              lemma_as_map_slot_key_equiv sts1 s2;
              assert(Spec.store_contains sts1_map k2);
              ()
            )
            else if Spec.store_contains sts1_map k2 then (
              let s2 = slot_of_key sts1 k2 in
              assert(get_slot sts s2 = get_slot sts1 s2);
              assert(stored_key sts s2 = k2);
              ()
            )
            else
              ()
          in
          forall_intro aux
        )
      )

let lemma_evictm_preserves_ismap
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (e:logS_entry _{EvictM_S? e})
  : Lemma (requires (S.is_map (thread_store vs)))
          (ensures (Valid? (verify_step vs e) ==> S.is_map (thread_store (verify_step vs e))))
  = ()

let lemma_evictm_simulates_spec
      (#vcfg:_)
      (vss:vtls vcfg{Valid? vss})
      (vsk:Spec.vtls)
      (e:logS_entry vcfg{EvictM_S? e})
  : Lemma (requires (let st = thread_store vss in
                     vtls_rel vss vsk /\
                     valid_logS_entry vss e /\
                     slot_points_to_is_merkle_points_to st /\
                     merkle_points_to_uniq st /\
                     merkle_points_to_desc st))
          (ensures (let ek = to_logK_entry vss e in
                    vtls_rel (verify_step vss e) (Spec.t_verify_step vsk ek))) =
  let sts = thread_store vss in
  let sts_map = as_map sts in
  let stk = Spec.thread_store vsk in
  let vss1 = verify_step vss e in
  let ek = to_logK_entry vss e in
  let vsk1 = Spec.t_verify_step vsk ek in
  match e with
  | EvictM_S s s' ->
    (* valid log entry e implies s and s' are inuse slots *)
    assert(inuse_slot sts s /\ inuse_slot sts s');

    let k = stored_key sts s in
    let k' = stored_key sts s' in

    assert(ek = Spec.EvictM k k');

    (* both spec and intermediate fail *)
    if not (is_proper_desc k k') then ()
    else if points_to_some_slot sts s Left || points_to_some_slot sts s Right then
      lemma_points_to_some_implies_has_instore_merkle_desc sts stk s
    else
      let d = desc_dir k k' in
      let v' = to_merkle_value (stored_value sts s') in
      let dh' = desc_hash_dir v' d in
      match dh' with
      | Empty -> ()
      | Desc k2 h2 b2 ->
        if k2 <> k then ()
        else if has_parent sts s && (parent_slot sts s <> s' || parent_dir sts s <> d) then (
          assert(parent_props_local sts s);
          if parent_slot sts s <> s' then (
            let sp = parent_slot sts s in
            let dp = parent_dir sts s in
            assert(points_to_dir sts sp dp s);
            let kp = stored_key sts sp in
            assert(kp <> k');
            assert(slot_points_to_is_merkle_points_to_local sts sp s dp);
            let vp = to_merkle_value (stored_value sts sp) in
            assert(mv_points_to vp dp k);
            assert(slot_points_to_is_merkle_points_to_local sts s' s d);
            assert(mv_points_to v' d k);
            assert(merkle_points_to_uniq_local sts sp s' k);
            ()
          )
          else (
            let od = parent_dir sts s in
            assert(points_to_dir sts s' od s);
            assert(slot_points_to_is_merkle_points_to_local sts s' s od);
            assert(mv_points_to v' od k);
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
            assert(mv_points_to v' d (stored_key sts s2));
            assert(mv_points_to v' d k);
            assert(k = stored_key sts s2);
            ()
          )
        )
        else if Spec.has_instore_merkle_desc stk k then
          lemma_has_instore_merkle_desc_implies_slot_points_to sts stk s

        else (
          assert(Valid? vss1);
          assert(Spec.Valid? vsk1);

          let sts1 = thread_store vss1  in
          lemma_evictm_preserves_ismap vss e;
          let sts1_map = as_map sts1 in
          let stk1 = Spec.thread_store vsk1 in
          let h = hashfn (stored_value sts s) in
          let v'_upd = Spec.update_merkle_value v' d k h false in
          let st_upd = update_value sts s' (MVal v'_upd) in
          assert(sts1 == mevict_from_store st_upd s s' d);
          let aux (k2: key):
            Lemma (ensures (sts1_map k2 = stk1 k2)) =
            if k2 = k then
              lemma_not_contains_after_mevict st_upd s s' d
            else if k2 = k' then
              ()
            else if Spec.store_contains stk1 k2 then (
              assert(stk1 k2 = stk k2);
              let s2 = slot_of_key sts k2 in
              assert(s2 <> s /\ s2 <> s');
              assert(get_slot sts s2 = get_slot sts1 s2);
              assert(stored_key sts1 s2 = k2);
              lemma_as_map_slot_key_equiv sts1 s2;
              assert(Spec.store_contains sts1_map k2);
              ()
            )
            else if Spec.store_contains sts1_map k2 then (
              let s2 = slot_of_key sts1 k2 in
              assert(get_slot sts s2 = get_slot sts1 s2);
              assert(stored_key sts s2 = k2);
              ()
            )
            else () in
          forall_intro aux
        )

let lemma_evictbm_preserves_ismap
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (e:logS_entry _{EvictBM_S? e})
  : Lemma (requires (S.is_map (thread_store vs)))
          (ensures (Valid? (verify_step vs e) ==> S.is_map (thread_store (verify_step vs e))))
  = ()

#push-options "--z3rlimit_factor 4"

let lemma_evictbm_simulates_spec
      (#vcfg:_)
      (vss:vtls vcfg{Valid? vss})
      (vsk:Spec.vtls)
      (e:logS_entry vcfg{EvictBM_S? e})
  : Lemma (requires (let sts = thread_store vss in
                     vtls_rel vss vsk /\
                     valid_logS_entry vss e /\
                     slot_points_to_is_merkle_points_to sts /\
                     merkle_points_to_uniq sts /\
                     merkle_points_to_desc sts))
          (ensures (let sts = thread_store vss in
                    let ek = to_logK_entry vss e in
                    vtls_rel (verify_step vss e) (Spec.t_verify_step vsk ek)))
  =
  let sts = thread_store vss in
  let sts_map = as_map sts in
  let stk = Spec.thread_store vsk in
  let vss1 = verify_step vss e in
  let ek = to_logK_entry vss e in
  let vsk1 = Spec.t_verify_step vsk ek in
  match e with
  | EvictBM_S s s' t ->

    (* otherwise valid_logS_entry would be false *)
    assert(inuse_slot sts s /\ inuse_slot sts s');

    let k = stored_key sts s in
    let k' = stored_key sts s' in
    assert(ek = Spec.EvictBM k k' t);

    if k = Root then ()
    else if not (thread_clock vss `ts_lt` t) then ()
    else if points_to_some_slot sts s Left || points_to_some_slot sts s Right then
      lemma_points_to_some_implies_has_instore_merkle_desc sts stk s
    else if Spec.has_instore_merkle_desc stk k then
      lemma_has_instore_merkle_desc_implies_slot_points_to sts stk s
    else if add_method_of sts s <> Spec.MAdd then ()
    else if not (is_proper_desc k k') then ()
    else (
      let v' = to_merkle_value (stored_value sts s') in
      let d = desc_dir k k' in
      let dh' = desc_hash_dir v' d in
      match dh' with
      | Empty -> ()
      | Desc k2 h2 b2 ->
        if k2 <> k || b2 then ()
        (* s' does not point to s in direction d *)
        else if not (points_to_dir sts s' d s) then (
          (* since s was added using merkle, our invariants say there is some slot that points to s *)
          let sa = pointing_slot sts s in
          assert(inuse_slot sts sa);

          (* sa points to s along direction da *)
          let da = if points_to_dir sts sa Left s then Left else Right in
          assert(points_to_dir sts sa da s);

          assert(slot_points_to_is_merkle_points_to_local sts sa s da);
          let ka = stored_key sts sa in
          let va = to_merkle_value (stored_value sts sa) in
          assert(mv_points_to va da k);
          assert(merkle_points_to_desc_local sts sa da);
          assert(not (empty_slot sts sa));
          assert(is_proper_desc k ka);
          assert(mv_points_to v' d k);
          assert(merkle_points_to_uniq_local sts s' sa k);
          assert(sa = s');

          ()
        )
        else (
          assert(Valid? vss1);
          assert(Spec.Valid? vsk1);
          let sts1 = thread_store vss1  in
          lemma_evictbm_preserves_ismap vss e;
          let sts1_map = as_map sts1 in
          let stk1 = Spec.thread_store vsk1 in

          let v'_upd = Spec.update_merkle_value v' d k h2 true in
          let sts_upd = update_value sts s' (MVal v'_upd) in
          assert(sts1 == mevict_from_store sts_upd s s' d);

          let aux (k2: key):
            Lemma (ensures (sts1_map k2 = stk1 k2)) =
            if k2 = k then (
              lemma_not_contains_after_mevict sts_upd s s' d;
              assert(not (store_contains_key sts1 k));
              ()
            )
            else if k2 = k' then
              ()
            else if Spec.store_contains stk1 k2 then (
              assert(stk1 k2 = stk k2);
              let s2 = slot_of_key sts k2 in
              assert(s2 <> s /\ s2 <> s');
              assert(get_slot sts s2 = get_slot sts1 s2);
              assert(stored_key sts1 s2 = k2);
              lemma_as_map_slot_key_equiv sts1 s2;
              assert(Spec.store_contains sts1_map k2);
              ()
            )
            else if Spec.store_contains sts1_map k2 then (
              let s2 = slot_of_key sts1 k2 in
              assert(get_slot sts s2 = get_slot sts1 s2);
              assert(stored_key sts s2 = k2);
              ()
            )
            else ()
          in
          forall_intro aux
        )
    )

#pop-options
