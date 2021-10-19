module Zeta.Intermediate.Verifier

open FStar.Classical

#push-options "--z3rlimit_factor 3 --query_stats"

let addm #vcfg (r:record vcfg.app) (s:slot_id vcfg)  (s':slot_id vcfg) (vs: vtls_t vcfg {vs.valid}):
  (vs': vtls_t vcfg {let a = AMP s r s' vs in
                   addm_precond a /\ addm_postcond a vs' \/
                   ~(addm_precond a) /\ ~vs'.valid}) =
  let a = AMP s r s' vs in
  let st = vs.st in
  let (gk,gv) = r in
  let k = to_base_key gk in
  if s = s' then fail vs
  (* check slot s' is not empty *)
  else if empty_slot st s' then fail vs
  else
    let k' = stored_base_key st s' in
    let v' = stored_value st s' in
    (* check k is a proper desc of k' *)
    if not (is_proper_desc k k') then fail vs
    (* check slot s is empty *)
    else if inuse_slot st s then fail vs
    (* check type of v is consistent with k *)
    else
      let v' = to_merkle_value v' in
      let d = desc_dir k k' in
      let dh' = desc_hash v' d in
      let h = hashfn gv in
      match dh' with
      | Empty -> (* k' has no child in direction d *)
        if not (is_init_record r) then fail vs
        else if points_to_some_slot st s' d then fail vs
        else
          let st = madd_to_store st s r s' d in
          let v' = Merkle.update_value v' d k Zeta.Hash.zero false in
          let st = update_value st s' (IntV v') in
          update_thread_store vs st
      | Desc k2 h2 b2 ->
        if k2 = k then (* k is a child of k' *)
          if not (h2 = h && b2 = false) then fail vs
          (* check slot s' does not contain a desc along direction d *)
          else if points_to_some_slot st s' d then fail vs
          else
            let st = madd_to_store st s r s' d in
            update_thread_store vs st
        else (* otherwise, k is not a child of k' *)
          (* first add must be init value *)
          if not (is_init_record r) then fail vs
          (* check k2 is a proper desc of k *)
          else if not (is_proper_desc k2 k) then fail vs
          else
            let d2 = desc_dir k2 k in
            let mv = to_merkle_value gv in
            let mv = Merkle.update_value mv d2 k2 h2 b2 in
            let v' = Merkle.update_value v' d k Zeta.Hash.zero false in
            let st =  if points_to_some_slot st s' d then
                        madd_to_store_split st s (gk, (IntV mv)) s' d d2
                      else
                        madd_to_store st s (gk, (IntV mv)) s' d in
            let st = update_value st s' (IntV v') in
            update_thread_store vs st

#pop-options

(* does a slot contain an app key *)
let contains_app_key (#vcfg:_) (st: vstore vcfg) (s: slot_id vcfg)
  = inuse_slot st s &&
    AppK? (stored_key st s)

(* a sequence of base keys contain only appln keys *)
let contains_only_app_keys (#vcfg:_) (st: vstore vcfg) (ss: S.seq (slot_id vcfg))
  = forall i. contains_app_key st (S.index ss i)

let contains_only_app_keys_comp (#vcfg:_) (st: vstore vcfg) (ss: S.seq (slot_id vcfg))
  : b:bool {b <==> contains_only_app_keys st ss}
  = let open Zeta.SeqIdx in
    not (exists_elems_with_prop_comp (fun s -> not (contains_app_key st s)) ss)

let puts (#vcfg:_)
  (vs: vtls_t vcfg{vs.valid})
  (ss: S.seq (slot_id vcfg))
  (ws: S.seq (app_value_nullable vcfg.app.adm))
  : vs': vtls_t vcfg{vs'.valid}
  = if contains_only_app_keys_comp vs.st ss && S.length ws = S.length ss then
       let st = puts_store vs.st ss ws in
       update_thread_store vs st
    else vs

let clock_is_monotonic
  (#vcfg:_)
  (e: GV.verifier_log_entry (int_verifier_spec_base vcfg))
  (vs: vtls_t vcfg)
  : Lemma (ensures (let vs_post = GV.verify_step e vs in
                    vs_post.valid ==> vs.clock `ts_leq` vs_post.clock))
  = ()

let lemma_int_verifier_clock_monotonic_prop (vcfg:_)
  : Lemma (ensures (GV.clock_monotonic_prop (int_verifier_spec_base vcfg)))
  = FStar.Classical.forall_intro_2 (clock_is_monotonic #vcfg)

let thread_id_is_constant
  (#vcfg:_)
  (e: GV.verifier_log_entry (int_verifier_spec_base vcfg))
  (vs: vtls_t vcfg)
  : Lemma (ensures (let vs_post = GV.verify_step e vs in
                    vs.tid = vs_post.tid))
  = ()

let lemma_int_verifier_thread_id_const_prop (vcfg:_)
  : Lemma (ensures (GV.thread_id_constant_prop (int_verifier_spec_base vcfg)))
  = FStar.Classical.forall_intro_2 (thread_id_is_constant #vcfg)

let evict_prop
  (#vcfg:_)
  (e: GV.verifier_log_entry (int_verifier_spec_base vcfg))
  (vs: vtls_t vcfg)
  : Lemma (ensures (let vs_post = GV.verify_step e vs in
                    GV.is_evict e ==>
                    vs_post.valid ==>
                    inuse_slot vs.st (GV.evict_slot e) /\
                    empty_slot vs_post.st (GV.evict_slot e)))
  = ()

let lemma_int_verifier_evict_prop (vcfg:_)
  : Lemma (ensures (GV.evict_prop (int_verifier_spec_base vcfg)))
  = FStar.Classical.forall_intro_2 (evict_prop #vcfg)

let add_prop
  (#vcfg:_)
  (e: GV.verifier_log_entry (int_verifier_spec_base vcfg))
  (vs: vtls_t vcfg)
  : Lemma (ensures (let vs_post = GV.verify_step e vs in
                    GV.is_add e ==>
                    vs_post.valid ==>
                    (empty_slot vs.st (GV.add_slot e)) /\
                    inuse_slot vs_post.st (GV.add_slot e)))
  = ()

let lemma_int_verifier_add_prop (vcfg:_)
  : Lemma (ensures (GV.add_prop (int_verifier_spec_base vcfg)))
  = FStar.Classical.forall_intro_2 (add_prop #vcfg)

let addb_prop
  (#vcfg:_)
  (e: GV.verifier_log_entry (int_verifier_spec_base vcfg))
  (vs: vtls_t vcfg)
  : Lemma (ensures (let vs_post = GV.verify_step e vs in
                    GV.is_blum_add e ==>
                    vs_post.valid ==>
                    GV.blum_add_timestamp e `ts_lt` vs_post.clock))
  = ()

let lemma_int_verifier_addb_prop (vcfg:_)
  : Lemma (ensures (GV.addb_prop (int_verifier_spec_base vcfg)))
  = FStar.Classical.forall_intro_2 (addb_prop #vcfg)

let evictb_prop
  (#vcfg:_)
  (e: GV.verifier_log_entry (int_verifier_spec_base vcfg))
  (vs: vtls_t vcfg)
  : Lemma (ensures (let vs_post = GV.verify_step e vs in
                    GV.is_blum_evict e ==>
                    vs_post.valid ==>
                    (vs.clock `ts_lt` vs_post.clock /\
                     vs_post.clock = GV.blum_evict_timestamp e)))
  = ()

let lemma_int_verifier_evictb_prop (vcfg:_)
  : Lemma (ensures (GV.evictb_prop (int_verifier_spec_base vcfg)))
  = FStar.Classical.forall_intro_2 (evictb_prop #vcfg)

let lemma_int_verifier (vcfg: verifier_config)
  : Lemma (ensures (GV.clock_monotonic_prop (int_verifier_spec_base vcfg) /\
                    GV.thread_id_constant_prop (int_verifier_spec_base vcfg) /\
                    GV.evict_prop (int_verifier_spec_base vcfg) /\
                    GV.add_prop (int_verifier_spec_base vcfg) /\
                    GV.addb_prop (int_verifier_spec_base vcfg) /\
                    GV.evictb_prop (int_verifier_spec_base vcfg)))
  = lemma_int_verifier_clock_monotonic_prop vcfg;
    lemma_int_verifier_thread_id_const_prop vcfg;
    lemma_int_verifier_evict_prop vcfg;
    lemma_int_verifier_add_prop vcfg;
    lemma_int_verifier_addb_prop vcfg;
    lemma_int_verifier_evictb_prop vcfg

let lemma_addm_props (#vcfg:_)
                     (vs':vtls_t vcfg{vs'.valid})
                     (e:logS_entry _{GV.AddM? e}):
  Lemma (requires ((GV.verify_step e vs').valid))
        (ensures (let GV.AddM (gk,gv) s s' = e in
                  let st' = vs'.st in
                  let k = to_base_key gk in
                  inuse_slot st' s' /\
                  (let k' = stored_base_key st' s' in
                   is_proper_desc k k' /\
                   is_merkle_key k' /\
                   (let mv' = to_merkle_value (stored_value st' s') in
                    let d = desc_dir k k' in
                    (Merkle.points_to_none mv' d ||
                     is_desc (Merkle.pointed_key mv' d) k)))))
  = let GV.AddM (gk,gv) s s' = e in
    let st' = vs'.st in
    let k = to_base_key gk in
    let k' = stored_base_key st' s' in
    assert(is_proper_desc k k');
    assert(is_merkle_key k');
    let mv' = to_merkle_value (stored_value st' s') in
    let d = desc_dir k k' in
    let dh' = desc_hash mv' d in
    match dh' with
    | Empty -> ()
    | Desc k2 _ _  ->
      if k2 = k then lemma_desc_reflexive k

let lemma_addm_identical_except2
  (#vcfg:_)
  (vs':vtls_t vcfg{vs'.valid})
  (e: logS_entry _ {GV.AddM? e})
  (s1:_):
  Lemma (requires (let GV.AddM _ s s' = e in
                  s1 <> s /\ s1 <> s' /\
                  (GV.verify_step e vs').valid))
        (ensures (let st' = vs'.st in
                  let vs = GV.verify_step e vs' in
                  let st = vs.st in
                  empty_slot st' s1 = empty_slot st s1 /\            // empty-ness unchanged
                  (inuse_slot st' s1 ==>
                   stored_key st' s1 = stored_key st s1 /\
                   stored_value st' s1 = stored_value st s1 /\
                   add_method_of st' s1 = add_method_of st s1 /\
                   points_to_info st' s1 Left = points_to_info st s1 Left /\
                   points_to_info st' s1 Right = points_to_info st s1 Right))) =
  match e with
  | GV.AddM r s s' ->
    let amp = AMP s r s' vs' in
    let vs = GV.verify_step e vs' in
    let gk,gv = r in
    let k = to_base_key gk in

    (* precond is satisfied since verify_step succeeds *)
    assert(addm_precond amp);

    let st' = addm_store_pre amp in
    let st = vs.st in
    let d = addm_dir amp in
    let mv' = addm_anc_val_pre amp in

    if Merkle.points_to_some mv' d then (
      if Merkle.points_to mv' d k then (
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

let lemma_runapp_preserves_ismap
      (#vcfg:_)
      (vs:vtls_t vcfg{vs.valid})
      (e:logS_entry _{GV.is_appfn e})
  : Lemma (requires (is_map (vs.st)))
          (ensures (let vs_ = GV.verify_step e vs in
                    vs_.valid ==> is_map vs_.st))
  = let vs_ = GV.verify_step e vs in
    if vs_.valid then (
      let st = vs.st in
      let st_ = vs_.st in
      let GV.RunApp f p ss = e in
      let fn = appfn f in
      let rs = GV.reads vs ss in
      let _,_,ws = fn p rs in
      assert(contains_only_app_keys_comp st ss);
      assert(st_ == puts_store st ss ws);
      ()
    )

(* if the key is not present in store and store is a map, then store remains a map after add *)
let lemma_vaddm_preserves_ismap_new_key
      (#vcfg:_)
      (vs:vtls_t vcfg{vs.valid})
      (e:logS_entry _{GV.AddM? e})
  : Lemma (requires (let st = vs.st in
                     let GV.AddM (gk,gv) _  _ = e in
                     let k = to_base_key gk in
                     is_map st /\ not (store_contains_key st k)))
          (ensures (let vs_ = GV.verify_step e vs in
                    vs_.valid ==> is_map vs_.st))
  = ()

let lemma_vaddb_preserves_ismap_new_key
      (#vcfg:_)
      (vs:vtls_t vcfg{vs.valid})
      (e:logS_entry _{GV.AddB? e})
  : Lemma (requires (let st = vs.st in
                     let GV.AddB (gk,_) _ _ _ = e in
                     let k = to_base_key gk in
                     is_map st /\ not (store_contains_key st k)))
          (ensures (let vs_ = GV.verify_step e vs in
                    vs_.valid ==> is_map vs_.st))
  = ()

let lemma_evictb_preserves_ismap
      (#vcfg:_)
      (vs:vtls_t vcfg{vs.valid})
      (e:logS_entry _{GV.EvictB? e})
  : Lemma (requires (is_map vs.st))
          (ensures (let vs_ = GV.verify_step e vs in
                    vs_.valid ==> is_map vs_.st))
  = ()

let lemma_evictm_preserves_ismap
      (#vcfg:_)
      (vs:vtls_t vcfg{vs.valid})
      (e:logS_entry _{GV.EvictM? e})
  : Lemma (requires (is_map vs.st))
          (ensures (let vs_ = GV.verify_step e vs in
                    vs_.valid ==> is_map vs_.st))
  = ()

let lemma_evictbm_preserves_ismap
      (#vcfg:_)
      (vs:vtls_t vcfg{vs.valid})
      (e:logS_entry _{GV.EvictBM? e})
  : Lemma (requires (is_map vs.st))
          (ensures (let vs_ = GV.verify_step e vs in
                    vs_.valid ==> is_map vs_.st))
  = ()

let lemma_nextepoch_preserves_ismap
      (#vcfg:_)
      (vs:vtls_t vcfg{vs.valid})
  : Lemma (requires (is_map vs.st))
          (ensures (let intspec = int_verifier_spec vcfg in
                    let vs_: vtls_t vcfg = GV.verify_step #intspec GV.NextEpoch vs in
                    vs_.valid ==> is_map vs_.st))
  = ()

let lemma_verifyepoch_preserves_ismap
      (#vcfg:_)
      (vs:vtls_t vcfg{vs.valid})
  : Lemma (requires (is_map vs.st))
          (ensures (let intspec = int_verifier_spec vcfg in
                    let vs_: vtls_t vcfg = GV.verify_step #intspec GV.VerifyEpoch vs in
                    vs_.valid ==> is_map vs_.st))
  = ()

#push-options "--fuel 0 --ifuel 0 --query_stats"

let lemma_verifiable_implies_slot_is_merkle_points_to_appfn
  (#vcfg:_)
  (vs:vtls_t vcfg)
  (e: logS_entry _ {GV.is_appfn e}):
  Lemma (requires (vs.valid /\ slot_points_to_is_merkle_points_to vs.st /\
                   (GV.verify_step e vs).valid))
        (ensures (let vs_ = GV.verify_step e vs in
                  slot_points_to_is_merkle_points_to vs_.st))
  = let vs_ = GV.verify_step e vs in
    let st = vs.st in
    let st_ = vs_.st in
    let GV.RunApp f p ss = e in
    let fn = appfn f in
    let rs = GV.reads vs ss in
    let _,_,ws = fn p rs in
    assert(contains_only_app_keys_comp st ss);
    assert(st_ == puts_store st ss ws);

    let merkle_implies_non_ref (s:_)
      : Lemma (requires (inuse_slot st s /\ is_merkle_key (stored_base_key st s)))
              (ensures (not (S.mem s ss)))
      = let k = stored_base_key st s in
        if S.mem s ss then (
          let i = S.index_mem s ss in
          assert(contains_app_key st (S.index ss i));
          ()
        )
    in

    let aux (s1 s2 d:_)
      : Lemma (ensures  (slot_points_to_is_merkle_points_to_local st_ s1 s2 d))
      = eliminate
        forall (s1 s2: slot_id _) (d:_). slot_points_to_is_merkle_points_to_local st s1 s2 d
        with s1 s2 d;
        puts_preserves st ss ws s1;
        puts_preserves st ss ws s2;
        if points_to_dir st_ s1 d s2 then (
          let k1 = stored_base_key st_ s1 in
          assert(is_merkle_key k1);
          merkle_implies_non_ref s1;
          puts_preserves_non_ref st ss ws s1
        )
    in
    forall_intro_3 aux

#pop-options


#push-options "--fuel 0 --ifuel 1 --query_stats"

let lemma_verifiable_implies_slot_is_merkle_points_to_addm
  (#vcfg:_)
  (vs:vtls_t vcfg)
  (e: logS_entry _ {GV.AddM? e}):
  Lemma (requires (vs.valid /\ slot_points_to_is_merkle_points_to vs.st /\
                   (GV.verify_step e vs).valid))
        (ensures (let vs_ = GV.verify_step e vs in
                  slot_points_to_is_merkle_points_to vs_.st))
  = let vs_ = GV.verify_step e vs in
    let st = vs.st in
    let st1 = vs_.st in
    let GV.AddM r s s' = e in
    let a = AMP s r s' vs in

    assert(vs_ == addm r s s' vs);
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
    forall_intro_3 aux

#pop-options

let lemma_verifiable_implies_slot_is_merkle_points_to_evictm
  (#vcfg:_)
  (vs:vtls_t vcfg)
  (e: logS_entry _{GV.EvictM? e})
  : Lemma (requires (vs.valid /\ slot_points_to_is_merkle_points_to vs.st /\
                   (GV.verify_step e vs).valid))
        (ensures (let vs1 = GV.verify_step e vs in
                  slot_points_to_is_merkle_points_to vs1.st)) =
  let vs1 = GV.verify_step e vs in
  let st1 = vs1.st in
  let st = vs.st in
  match e with
  | GV.EvictM s s' ->
    assert(empty_slot st1 s);
    assert(identical_except2 st st1 s s');
    let k = stored_base_key st s in
    let k' = stored_base_key st s' in
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
          assert(slot_points_to_is_merkle_points_to_local st s1 s2 dx);
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
                                                      (vs:vtls_t vcfg)
                                                      (e: logS_entry _{GV.AddB? e}):
  Lemma (requires (vs.valid /\ slot_points_to_is_merkle_points_to vs.st /\
                   (GV.verify_step e vs).valid))
        (ensures (let vs1 = GV.verify_step e vs in
        slot_points_to_is_merkle_points_to vs1.st)) =
  let vs1 = GV.verify_step e vs in
  let st1 = vs1.st in
  let st = vs.st in

  match e with
  | GV.AddB (k,v) s  _ _  ->
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
                                                      (vs:vtls_t vcfg)
                                                      (e: logS_entry _{GV.EvictB? e}):
  Lemma (requires (vs.valid /\ slot_points_to_is_merkle_points_to vs.st /\
                   (GV.verify_step e vs).valid))
        (ensures (slot_points_to_is_merkle_points_to (GV.verify_step e vs).st)) =
  let vs1 = GV.verify_step e vs in
  let st1 = vs1.st in
  let st = vs.st in

  match e with
  | GV.EvictB s  _  ->
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

let lemma_verifiable_implies_slot_is_merkle_points_to_evictbm (#vcfg:_)
                                                      (vs:vtls_t vcfg)
                                                      (e: logS_entry _{GV.EvictBM? e}):
  Lemma (requires (vs.valid /\ slot_points_to_is_merkle_points_to vs.st /\
                   (GV.verify_step e vs).valid))
        (ensures (slot_points_to_is_merkle_points_to (GV.verify_step e vs).st)) =
  let vs1 = GV.verify_step e vs in
  let st1 = vs1.st in
  let st = vs.st in

  match e with
  | GV.EvictBM s s'  _  ->
    assert(identical_except2 st1 st s s');
    let k = stored_base_key st s in
    let k' = stored_base_key st s' in
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

let lemma_verifiable_implies_slot_is_merkle_points_to (#vcfg:_)
                                                      (vs:vtls_t vcfg)
                                                      (e: logS_entry _):
  Lemma (requires (vs.valid /\ slot_points_to_is_merkle_points_to vs.st /\
                   (GV.verify_step e vs).valid))
        (ensures (let vs_ = GV.verify_step e vs in
                  slot_points_to_is_merkle_points_to vs_.st))
  = let open Zeta.GenericVerifier in
    match e with
    | RunApp _ _ _ -> lemma_verifiable_implies_slot_is_merkle_points_to_appfn vs e
    | AddM _ _ _ -> lemma_verifiable_implies_slot_is_merkle_points_to_addm vs e
    | AddB _ _ _ _ -> lemma_verifiable_implies_slot_is_merkle_points_to_addb vs e
    | EvictM _ _ -> lemma_verifiable_implies_slot_is_merkle_points_to_evictm vs e
    | EvictB _ _ -> lemma_verifiable_implies_slot_is_merkle_points_to_evictb vs e
    | EvictBM _ _ _ -> lemma_verifiable_implies_slot_is_merkle_points_to_evictbm vs e
    | _ -> ()
