module Zeta.High.Interleave

open FStar.Classical

let root : r:Zeta.BinTree.bin_tree_node { Zeta.BinTree.depth r = 0 } = Zeta.BinTree.Root

#push-options "--fuel 0 --ifuel 1 --query_stats"

let runapp_refs_only_leafkeys (#app #n:_) (il: verifiable_log app n) (i:_ {RunApp? (index il i)}) (k: base_key)
  : Lemma (ensures (let e = index il i in
                    e `refs_key` k ==> is_leaf_key k))
  = let e = index il i in
    lemma_cur_thread_state_extend il i;
    let RunApp f p ss = e in
    let vs_pre = thread_state_pre (src il i) il i in
    if e `refs_key` k then
      let idx = index_mem k ss in
      runapp_implies_store_contains e vs_pre k

#push-options "--z3rlimit_factor 3"

let not_refs_implies_store_unchanged  (#app #n:_) (ki:base_key) (ti:nat{ti < n})
  (il: verifiable_log app n) (i:seq_index il)
  : Lemma (ensures (let e = index il i in
                    let st_pre = thread_store_pre ti il i in
                    let st_post = thread_store_post ti il i in
                    not (e `exp_refs_key` ki) ==>
                    store_contains st_pre ki ==>
                    (store_contains st_post ki /\
                     stored_key st_post ki == stored_key st_pre ki /\
                     stored_value st_post ki == stored_value st_pre ki)))
  = let e = index il i in
    let t = src il i in
    let st_pre = thread_store_pre ti il i in
    let vs_pre = thread_state_pre ti il i in
    lemma_cur_thread_state_extend il i;

    if t <> ti then lemma_non_cur_thread_state_extend ti il i
    else
      if not (e `exp_refs_key` ki) && store_contains st_pre ki then
        match e with
        | RunApp _ _ _ ->
          runapp_doesnot_change_nonref_slots e vs_pre ki
        | _ -> ()

#pop-options

let not_refs_implies_store_containment_unchanged  (#app #n:_) (ki:base_key) (ti:nat{ti < n})
  (il: verifiable_log app n) (i:seq_index il)
  : Lemma (ensures (let e = index il i in
                    let st_pre = thread_store_pre ti il i in
                    let st_post = thread_store_post ti il i in
                    not (e `refs_key` ki) ==>
                    store_contains st_pre ki = store_contains st_post ki))
  = let e = index il i in
    let t = src il i in
    let st_pre = thread_store_pre ti il i in
    let vs_pre = thread_state_pre ti il i in
    lemma_cur_thread_state_extend il i;

    if t <> ti then lemma_non_cur_thread_state_extend ti il i
    else
      match e with
      | RunApp _ _ _ ->
          runapp_doesnot_change_slot_emptiness e vs_pre ki
      | _ ->
        ()

#restart-solver

#push-options "--z3rlimit_factor 3"

let not_refs_implies_store_key_unchanged  (#app #n:_) (ki:base_key) (ti:nat{ti < n})
  (il: verifiable_log app n) (i:seq_index il)
  : Lemma (ensures (let e = index il i in
                    let st_pre = thread_store_pre ti il i in
                    let st_post = thread_store_post ti il i in
                    not (e `refs_key` ki) ==>
                    store_contains st_pre ki ==>
                    store_contains st_post ki /\
                    stored_key st_pre ki = stored_key st_post ki /\
                    add_method_of st_pre ki = add_method_of st_post ki))
  = let e = index il i in
    let t = src il i in
    let st_pre = thread_store_pre ti il i in
    let vs_pre = thread_state_pre ti il i in
    lemma_cur_thread_state_extend il i;
    not_refs_implies_store_containment_unchanged ki ti il i;

    if t <> ti then lemma_non_cur_thread_state_extend ti il i
    else
      match e with
      | RunApp _ _ _ -> runapp_doesnot_change_slot_key ki e vs_pre;
                        runapp_doesnot_change_store_addmethod ki e vs_pre
      | _ -> ()

#pop-options

let runapp_doesnot_change_store_keys_extended (#app #n:_) (k:base_key)
  (il: verifiable_log app n) (i: seq_index il {is_appfn il i})
  : Lemma (ensures (let t = I.src il i in
                    let st_pre = thread_store_pre t il i in
                    let st_post = thread_store_post t il i in
                    store_contains st_post k = store_contains st_pre k /\
                    (store_contains st_pre k ==>
                    (stored_key st_pre k = stored_key st_post k /\
                     add_method_of st_pre k = add_method_of st_post k))))
  = let e = index il i in
    let t = src il i in
    let vs_pre = thread_state_pre t il i in
    lemma_cur_thread_state_extend il i;
    runapp_doesnot_change_slot_emptiness e vs_pre k;
    runapp_doesnot_change_slot_key k e vs_pre;
    runapp_doesnot_change_store_addmethod k e vs_pre

let runapp_doesnot_change_store_keys (#app #n:_) (k:base_key)
  (il: verifiable_log app n) (i: seq_index il {is_appfn il i})
  : Lemma (ensures (let t = src il i in
                    let st_pre = thread_store_pre t il i in
                    let st_post = thread_store_post t il i in
                    store_contains st_post k = store_contains st_pre k))
  = runapp_doesnot_change_store_keys_extended k il i

let blum_evict_elem_props
  (#app #n:_)
  (il: verifiable_log app n)
  (i: seq_index il {is_blum_evict il i})
  : Lemma (ensures (let e = I.index il i in
                    let MSD.MHDom (gk,vk) t_e tid_e = blum_evict_elem il i in
                    let tid = I.src il i in
                    let st_pre = thread_store_pre tid il i in
                    let k = V.evict_slot e in
                    k = to_base_key gk /\
                    store_contains st_pre k /\
                    gk = stored_key st_pre k /\
                    vk = stored_value st_pre k /\
                    t_e = V.blum_evict_timestamp e /\
                    tid_e = tid))
  = let e = index il i in
    let be = blum_evict_elem il i in
    lemma_cur_thread_state_extend il i

let mk_vlog_entry_ext #app #n (il: verifiable_log app n) (i: seq_index il)
  = let vle = I.index il i in
    let open Zeta.GenericVerifier in
    let open Zeta.High.Verifier in
    let vs = cur_thread_state_pre il i in
    let tid = src il i in
    lemma_cur_thread_state_extend il i;

    match vle with
    | EvictM k k' ->
      let v = stored_value vs.st k in
      EvictMerkle vle v
    | EvictB k ts ->
      let v = stored_value vs.st k in
      EvictBlum vle v tid
    | EvictBM k _ ts ->
      let v = stored_value vs.st k in
      EvictBlum vle v tid
    | RunApp f p ss ->
      let rs = reads vs ss in
      App vle rs
    | v -> NEvict v

let vlog_entry_ext_prop (#app #n:_) (il: verifiable_log app n) (i: seq_index il)
  : Lemma (ensures (let ee = mk_vlog_entry_ext il i in
                    let e = I.index il i in
                    e = to_vlog_entry ee))
  = ()

let mk_vlog_entry_ext_pp (#app #n:_) (il: verifiable_log app n) (j:nat{j <= length il}) (i:nat{i < j})
  : Lemma (ensures (let il' = prefix il j in
                    mk_vlog_entry_ext il i = mk_vlog_entry_ext il' i))
  = ()

let vlog_ext_of_il_log (#app: app_params) (#n:nat) (il: verifiable_log app n)
  : seq (vlog_entry_ext app)
  = S.init (length il) (mk_vlog_entry_ext il)

let vlog_ext_prefix_property (#app #n:_) (il: verifiable_log app n) (j:nat{j <= length il})
  : Lemma (ensures (let il' = prefix il j in
                    let le'1 = vlog_ext_of_il_log il' in
                    let le = vlog_ext_of_il_log il in
                    let le'2 = SA.prefix le j in
                    le'1 = le'2))
          [SMTPat (vlog_ext_of_il_log (prefix il j))]
  = let il' = prefix il j in
    let le1 = vlog_ext_of_il_log il' in
    let le = vlog_ext_of_il_log il in
    let le2 = SA.prefix le j in
    assert(S.length le1 = S.length le2);
    let aux (i: SA.seq_index le1)
      : Lemma (ensures (S.index le1 i = S.index le2 i))
      = ()
    in
    introduce forall i. (S.index le1 i = S.index le2 i) with aux i;
    assert(equal le1 le2)

let is_eac #app #n (il: verifiable_log app n)
  = is_eac_log (vlog_ext_of_il_log il)

let lemma_eac_empty #app #n (il: verifiable_log app n{S.length il = 0})
  : Lemma (ensures (is_eac il))
  = let le = vlog_ext_of_il_log il in
    eac_empty_log le

let eac_state_of_key (#app #n:_) (k: base_key) (il: verifiable_log app n)
  : eac_state app k
  = EAC.eac_state_of_key k (vlog_ext_of_il_log il)

let empty_implies_eac (#app #n:_) (il: verifiable_log app n)
  : Lemma (ensures (length il = 0 ==> is_eac il))
  = if length il = 0 then
      let le = vlog_ext_of_il_log il in
      eac_empty_log le

let eac_state_empty (#app #n:_) (k: base_key)
  (il: verifiable_log app n{length il = 0})
  : Lemma (ensures (eac_state_of_key k il = EACInit))
  = empty_log_implies_init_state k (vlog_ext_of_il_log il)

let eac_state_snoc (#app #n:_) (k: base_key)
  (il: verifiable_log app n{length il > 0})
  : Lemma (ensures (let i = length il - 1  in
                    let il' = prefix il i in
                    let es' = eac_state_of_key k il' in
                    let es = eac_state_of_key k il in
                    let ee = mk_vlog_entry_ext il i in
                    es == eac_add ee es'))
  = let i = length il - 1 in
    let il' = prefix il i in
    let le = vlog_ext_of_il_log il in
    let le' = vlog_ext_of_il_log il' in
    eac_state_transition k le

let eac_state_transition (#app #n:_) (k: base_key)
  (il: verifiable_log app n) (i: seq_index il)
  : Lemma (ensures (let es_pre =  eac_state_of_key_pre k il i in
                    let es_post = eac_state_of_key_post k il i in
                    let smk = eac_smk app k in
                    let ee = mk_vlog_entry_ext il i in
                    es_post = eac_add ee es_pre))
  = let il2 = prefix il (i+1) in
    eac_state_snoc k il2

let lemma_eac_implies_prefix_eac (#app #n:_) (il: verifiable_log app n) (i: nat{i <= S.length il})
  : Lemma (ensures (is_eac il ==> is_eac (prefix il i)))
  = ()


let eac_implies_eac_state_valid (#app #n:_) (k: base_key)
  (il: verifiable_log app n)
  : Lemma (ensures (is_eac il ==> eac_state_of_key k il <> EACFail))
  = ()

#push-options "--fuel 1"

let rec eac_state_of_root_init (#app #n:_) (il: eac_log app n)
  : Lemma (ensures (eac_state_of_key root il = EACInit))
          (decreases (length il))
  = let open Zeta.BinTree in
    if length il = 0 then
      eac_state_empty root il
    else (
      let i = length il - 1  in
      let il' = prefix il i in
      eac_state_of_root_init il';
      eac_state_snoc root il;
      lemma_cur_thread_state_extend il i
    )

#pop-options

open Zeta.SeqIdx

let rec eac_state_active_implies_prev_add (#app #n:_) (k: base_key) (il: eac_log app n)
  : Lemma (ensures (is_eac_state_active k il <==> has_some_add_of_key k il))
          (decreases (length il))
  = if length il = 0 then
      eac_state_empty k il
    else (
      let i = length il - 1 in
      let es = eac_state_of_key k il in
      let il' = prefix il i in
      let es' = eac_state_of_key k il' in
      eac_state_snoc k il;
      eac_state_active_implies_prev_add k il';

      if is_eac_state_active k il' then
        let j = last_idx (HV.is_add_of_key k) (i_seq il) in
        exists_elems_with_prop_intro (HV.is_add_of_key k) (i_seq il) j
      else if is_eac_state_active k il then
        exists_elems_with_prop_intro (HV.is_add_of_key k) (i_seq il) i
      else (
        assert(forall i. not (HV.is_add_of_key k (index il' i)));
        let aux (j: seq_index il)
          : Lemma (ensures (not (HV.is_add_of_key k (index il j))))
          = if j < i then
              assert(not (HV.is_add_of_key k (index il' j)))
        in
        forall_intro aux
      )
    )

let eac_state_active_implies_prev_add2 (#app #n:_) (k: base_key) (il: eac_log app n)
  : Lemma (ensures (is_eac_state_active k il <==> has_some_add_of_key k il))
          [SMTPat (eac_state_of_key k il)]
  = eac_state_active_implies_prev_add k il

#push-options "--z3rlimit_factor 3"

let rec eac_state_init_implies_no_key_refs (#app #n:_) (k: base_key) (il: eac_log app n)
  : Lemma (ensures (eac_state_of_key k il = EACInit ==> ~ (has_some_ref_to_key k il)))
          (decreases (length il))
  = if length il = 0 then
      eac_state_empty k il
    else (
      let i = length il - 1 in
      let es = eac_state_of_key k il in
      let il' = prefix il i in
      let es' = eac_state_of_key k il' in
      eac_state_snoc k il;
      eac_state_init_implies_no_key_refs k il';

      if es = EACInit then (
        assert(es' = EACInit);
        assert(forall i. not (index il' i `refs_key` k));
        let aux (j: seq_index il)
          : Lemma (ensures (not (index il j `refs_key` k)))
          = if j < i then
              assert(not (index il' j `refs_key` k))
        in
        forall_intro aux
      )
    )

#pop-options

open Zeta.BinTree

let eac_storage_prop (#app #n:_)(k: base_key {k <> Root}) (il: eac_log app n)
  = let es = eac_state_of_key k il in
    let is = i_seq il in
    match es with
      | EACInStore _ gk _ ->
        let i = last_idx (HV.is_add_of_key k) is in
        let t = src il i in
        store_contains (thread_store t il) k /\
        stored_key (thread_store t il) k = gk /\
        (forall t'. t' <> t ==> not (store_contains (thread_store t' il) k))
        | _ -> (forall t. not (store_contains (thread_store t il) k))

let eac_storage_prop_implies_store_contains_implies
  (#app #n:_)
  (k: base_key {k <> Root})
  (il: eac_log app n {eac_storage_prop k il})
  (t:nat{t < n})
  : Lemma (ensures (let st = thread_store t il in
                    let es = eac_state_of_key k il in
                    store_contains st k ==>
                    EACInStore? es))
  = ()

#pop-options

#push-options "--z3rlimit_factor 3"

let eac_storage_prop_snoc_appfn
  (#app #n:_)
  (ki: base_key {ki <> root}) (il: eac_log app n {length il > 0})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     let e = index il i in
                     RunApp? e /\ e `refs_key` ki /\ eac_storage_prop ki il'))
          (ensures (eac_storage_prop ki il))
  = let i = length il - 1 in
    let is = i_seq il in
    let t = src il i in
    let es = eac_state_of_key ki il in
    let st = thread_store t il in
    let vs = thread_state t il in

    let il' = prefix il i in
    let is' = i_seq il' in
    let es' = eac_state_of_key ki il' in
    let st' = thread_store t il' in
    let vs' = thread_state t il' in
    let e = index il i in

    eac_state_snoc ki il;
    lemma_cur_thread_state_extend il i;
    SA.lemma_fullprefix_equal il;

    assert(vs' == cur_thread_state_pre il i);
    assert(vs == cur_thread_state_post il i);
    assert(vs == verify_step e vs');

    runapp_implies_store_contains e vs' ki;
    assert(store_contains st' ki);
    runapp_doesnot_change_slot_key ki e vs';
    assert(store_contains st ki);
    assert(stored_key st ki = stored_key st' ki);

    assert(EACInStore? es');
    let j = last_idx (HV.is_add_of_key ki) is' in
    assert(EACInStore? es);
    last_idx_snoc (HV.is_add_of_key ki) is;
    assert(j = last_idx (HV.is_add_of_key ki) is);

    let aux ()
      : Lemma (ensures (t = src il j))
      = let tj = src il j in
        if tj <> t then
          eliminate forall t'. t' <> tj ==> not (store_contains (thread_store t' il') ki) with t
    in
    aux();

    let aux (t':_)
      : Lemma (ensures (t' <> t ==> not (store_contains (thread_store t' il) ki)))
      = if t' <> t then
          //assert(not (store_contains (thread_store t' il') ki));
          lemma_non_cur_thread_state_extend t' il i
    in
    forall_intro aux

#pop-options

#push-options "--z3rlimit_factor 5"

let eac_storage_prop_snoc_evict
  (#app #n:_)
  (ki: base_key {ki <> Zeta.BinTree.Root}) (il: eac_log app n {length il > 0})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     let e = index il i in
                     is_evict e /\ e `refs_key` ki /\ eac_storage_prop ki il'))
          (ensures (eac_storage_prop ki il))
  = let i = length il - 1 in
    let is = i_seq il in
    let t = src il i in
    let es = eac_state_of_key ki il in
    let il' = prefix il i in
    let es' = eac_state_of_key ki il' in
    let e = index il i in
    let k = evict_slot e in
    assert(k = ki);

    (* since we just saw a addm, the state is EACInStore *)
    eac_state_snoc k il;
    lemma_cur_thread_state_extend il i;
    let st' = thread_store t il' in
    assert(store_contains st' k);
    eac_storage_prop_implies_store_contains_implies k il' t;

    (* es is one of EACEvicted* *)
    assert(not (EACInStore? es));

    let aux (t':_)
      : Lemma (ensures (not (store_contains (thread_store t' il) k)))
      = if t' <> t then
          lemma_non_cur_thread_state_extend t' il i
          //assert(not (store_contains (thread_store t' il') k));
          //()
    in
    forall_intro aux

#pop-options

#push-options "--z3rlimit_factor 3"

let eac_storage_prop_snoc_non_ref
  (#app #n:_)
  (k: base_key {k <> Zeta.BinTree.Root})
  (il: eac_log app n{length il > 0})
  : Lemma (requires (let i = length il - 1 in
                     let e = index il i in
                     let il' = prefix il i in
                     not (e `refs_key` k) /\ eac_storage_prop k il'))
          (ensures (eac_storage_prop k il))
  = let i = length il - 1 in
    let e = index il i in
    let t = src il i in
    let is = i_seq il in
    let es = eac_state_of_key k il in
    let il' = prefix il i in
    let is' = i_seq il' in
    let es' = eac_state_of_key k il' in
    eac_state_snoc k il;
    assert(es = es');
    match es with
    | EACInStore _ gk _ ->
      let j = last_idx (HV.is_add_of_key k) is' in
      exists_elems_with_prop_intro (HV.is_add_of_key k) is j;
      last_idx_snoc (HV.is_add_of_key k) is;
      assert(j = last_idx (HV.is_add_of_key k) is);

      let t = src il j in
      not_refs_implies_store_key_unchanged k t il i;

      let aux (t':_)
        : Lemma (ensures (t' <> t ==> not (store_contains (thread_store t' il) k)))
        = if t' <> t then (
            assert (not (store_contains (thread_store t' il') k));
            not_refs_implies_store_containment_unchanged k t' il i
          )
      in
      forall_intro aux
    | _ ->
      let aux (t:_)
        : Lemma (ensures (not (store_contains (thread_store t il) k)) )
        = not_refs_implies_store_containment_unchanged k t il i
      in
      forall_intro aux

#pop-options

#push-options "--z3rlimit_factor 3"

let eac_storage_prop_snoc_add
  (#app #n:_)
  (ki: base_key {ki <> Zeta.BinTree.Root}) (il: eac_log app n {length il > 0})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     let e = index il i in
                     is_add e /\ e `refs_key` ki /\ eac_storage_prop ki il'))
          (ensures (eac_storage_prop ki il))
  = let i = length il - 1 in
    let is = i_seq il in
    let t = src il i in
    let es = eac_state_of_key ki il in
    let il' = prefix il i in
    let e = index il i in
    let k = add_slot e in
    assert(k = ki);

    (* since we just saw a addm, the state is EACInStore *)
    eac_state_snoc k il;
    lemma_cur_thread_state_extend il i;

    let EACInStore _ gk _ = es in
    let st = thread_store t il in

    assert(store_contains st k);
    assert(stored_key st k = gk);
    exists_elems_with_prop_intro (HV.is_add_of_key k) is i;
    assert(has_some_add_of_key k il);
    last_idx_snoc (HV.is_add_of_key k) is;
    assert(last_idx (HV.is_add_of_key k) is = i);

    let aux (t':_)
      : Lemma (ensures (t' <> t ==> not (store_contains (thread_store t' il) k)))
      = if t' <> t then lemma_non_cur_thread_state_extend t' il i
    in
    forall_intro aux

#pop-options

let init_thread_store_contains_no_key (#app #n:_)
  (t:nat{t < n})
  (k: base_key {k <> Root})
  (il: eac_log app n {length il = 0})
  : Lemma (ensures (let st = thread_store t il in
                    not (store_contains st k)))
  = let vspec = high_verifier_spec app in
    lemma_length0_implies_empty il;
    lemma_empty_sseq (verifier_log_entry vspec) n t

let rec eac_storage_lemma (#app #n:_) (k: base_key {k <> Zeta.BinTree.Root}) (il: eac_log app n)
  : Lemma (ensures (eac_storage_prop k il))
          (decreases (length il))
  = let es = eac_state_of_key k il in
    let is = i_seq il in
    if length il = 0 then (
      eac_state_empty k il;
      let aux (t:_)
        : Lemma (ensures (not (store_contains (thread_store t il) k)))
        = init_thread_store_contains_no_key t k il
      in
      forall_intro aux
    )
    else (
      let i = length il - 1 in
      let e = index il i in
      let t = src il i in
      let il' = prefix il i in
      let es' = eac_state_of_key k il' in
      eac_state_snoc k il;
      eac_storage_lemma k il';
      if e `refs_key` k then (
        match e with
        | AddB _ _ _ _
        | AddM _ _ _ -> eac_storage_prop_snoc_add k il
        | EvictBM _ _ _
        | EvictB _ _
        | EvictM _ _ -> eac_storage_prop_snoc_evict k il
        | NextEpoch
        | VerifyEpoch -> eac_storage_prop_snoc_non_ref k il
        | RunApp _ _ _ -> eac_storage_prop_snoc_appfn k il
      )
      else
        eac_storage_prop_snoc_non_ref k il
    )

let root_storage_prop (#app:_) (#n:nat{n > 0}) (il: eac_log app n)
  = store_contains (thread_store 0 il) Root /\
    stored_key (thread_store 0 il) Root = IntK Root /\
    (forall t. t <> 0 ==> not (store_contains (thread_store t il) Root))

let root_storage_prop_init (#app:_) (#n:pos) (il: eac_log app n{length il = 0})
  : Lemma (ensures (root_storage_prop il))
  = let vspec = high_verifier_spec app in
    lemma_length0_implies_empty il;
    lemma_empty_sseq (verifier_log_entry vspec) n 0;
    let aux (t:_)
      : Lemma (ensures (t <> 0 ==> not (store_contains (thread_store t il) Root)))
      = lemma_empty_sseq (verifier_log_entry vspec) n t
    in
    forall_intro aux

let root_storage_prop_snoc (#app:_) (#n:pos) (il: eac_log app n{length il > 0})
  : Lemma (requires (root_storage_prop (prefix il (length il - 1))))
          (ensures (root_storage_prop il))
  = let i = length il - 1 in
    let e = index il i in
    let t = src il i in
    let il' = prefix il i in
    eac_state_snoc Root il;
    eac_state_of_root_init il;

    not_refs_implies_store_key_unchanged Root 0 il i;
    let aux (t:_)
      : Lemma (ensures(t <> 0 ==> not (store_contains (thread_store t il) Root)))
      = if t <> 0 then
          not_refs_implies_store_containment_unchanged Root t il i
    in
    forall_intro aux

let rec lemma_root_storage_prop (#app:_) (#n:pos) (il: eac_log app n)
  : Lemma (ensures (root_storage_prop il))
          (decreases (length il))
  = if length il = 0 then root_storage_prop_init il
    else (
      let i = length il - 1 in
      let il' = prefix il i in
      lemma_root_storage_prop il';
      root_storage_prop_snoc il
    )

(* when the eac_state of k is instore, then k is in the store of a unique verifier thread *)
let stored_tid (#app:_) (#n:pos) (k: base_key) (il: eac_log app n {is_eac_state_instore k il})
  : Tot (tid:nat{tid < n /\
          (let st = thread_store tid il in
           let es = eac_state_of_key k il in
           let gk = to_gen_key es in
           store_contains st k /\ gk = stored_key st k)})
  = if k = Root then (
      lemma_root_storage_prop il;
      0
    )
    else (
      eac_storage_lemma k il;
      let i = last_idx (HV.is_add_of_key k) (i_seq il) in
      src il i
    )

let lemma_instore (#app:_) (#n:pos) (bk: base_key) (il: eac_log app n)
  : Lemma (ensures (exists_in_some_store bk il <==> is_eac_state_instore bk il))
  = eac_state_of_root_init il;
    let es = eac_state_of_key bk il in
    if is_eac_state_instore bk il then
      exists_intro (fun t -> store_contains (thread_store t il) bk) (stored_tid bk il)
    else
      //assert(bk <> Root);
      eac_storage_lemma bk il

(* uniqueness: k is never in two stores *)
let key_in_unique_store (#app #n:_) (k:base_key) (il: eac_log app n) (tid1 tid2: thread_id il)
  : Lemma (ensures (tid1 <> tid2 ==>
                    ~ (store_contains (thread_store tid1 il) k /\ store_contains (thread_store tid2 il) k)))
  = lemma_root_storage_prop il;

    if tid1 <> tid2 && store_contains (thread_store tid1 il) k then (
      if k = Root then (
        if tid1 = 0 then
          eliminate forall t. t <> 0 ==> not (store_contains (thread_store t il) Root) with tid2
        else
          eliminate forall t. t <> 0 ==> not (store_contains (thread_store t il) Root) with tid1
      )
      else (
        eac_storage_lemma k il;
        eac_storage_prop_implies_store_contains_implies k il tid1;
        eliminate forall t. t <> tid1 ==> not (store_contains (thread_store t il) k) with tid2
      )
    )

let lemma_root_in_store0 (#app #n:_) (il: eac_log app n)
  : Lemma (requires (n > 0))
          (ensures (store_contains (thread_store 0 il) Zeta.BinTree.Root))
  = lemma_root_storage_prop il

let lemma_root_not_in_store (#app #n:_) (tid: nat{tid < n /\ tid > 0}) (il: eac_log app n)
  : Lemma (not (store_contains (thread_store tid il) Zeta.BinTree.Root))
  = lemma_root_storage_prop il;
    eliminate forall t. t <> 0 ==> not (store_contains (thread_store t il) Root) with tid

let eac_value (#app #n:_) (k: key app) (il: eac_log app n)
  : value_t k
  = eac_state_of_root_init il;
    let bk = to_base_key k in
    let es = eac_state_of_key bk il in
    match es with
    | EACInit ->
      if k = IntK Root then stored_value k il
      else init_value k
    | EACInStore _ gk _ ->
      if gk = k then stored_value k il
      else init_value k
    | EACEvictedMerkle gk gv ->
      if gk = k then gv
      else init_value k
    | EACEvictedBlum gk gv _ _ ->
      if gk = k then gv
      else init_value k

let eac_value_is_stored_value (#app #n:_) (il: eac_log app n) (gk: key app) (tid: nat {tid < n})
  : Lemma (requires (let bk = to_base_key gk in
                     store_contains (thread_store tid il) bk /\
                     stored_key (thread_store tid il) bk = gk))
          (ensures (let bk = to_base_key gk in
                    eac_value gk il = HV.stored_value (thread_store tid il) bk))
  = eac_state_of_root_init il;
    lemma_root_storage_prop il;

    let k = to_base_key gk in
    let es = eac_state_of_key k il in
    if k = Root then
      key_in_unique_store k il tid 0
    else (
      eac_storage_lemma k il;
      eac_storage_prop_implies_store_contains_implies k il tid;
      key_in_unique_store k il tid (stored_tid k il)
    )

let eac_value_is_stored_value_int (#app #n:_) (il: eac_log app n) (k: merkle_key) (tid: nat{ tid < n })
  : Lemma (requires (store_contains (thread_store tid il) k))
          (ensures (eac_value (IntK k) il = HV.stored_value (thread_store tid il) k))
  = eac_value_is_stored_value il (IntK k) tid

let eac_value_is_evicted_value (#app #n:_) (il: eac_log app n) (gk: key app):
  Lemma (requires (let bk = to_base_key gk in
                   let es = eac_state_of_key bk il in
                   is_eac_state_evicted bk il /\
                   gk = to_gen_key es))
        (ensures (let bk = to_base_key gk in
                  let es = eac_state_of_key bk il in
                  eac_state_evicted_value es = eac_value gk il))
  = ()

let eac_value_init_state_is_init (#app #n:_) (il: eac_log app n) (gk: key app):
  Lemma (requires (let bk = to_base_key gk in
                   let es = eac_state_of_genkey gk il in
                   es = EACInit /\
                   bk <> Zeta.BinTree.Root))
        (ensures (eac_value gk il = init_value gk))
  = ()

let eac_value_init
  (#app #n:_)
  (gk: key app)
  (il: eac_log app n {length il = 0})
  : Lemma (ensures (eac_value gk il = init_value gk))
  = let bk = to_base_key gk in
    let vspec = high_verifier_spec app in
    eac_state_empty bk il;
    lemma_root_storage_prop il;

    if bk = Root then (
      eac_value_is_stored_value il gk 0;
      lemma_length0_implies_empty il;
      lemma_empty_sseq (verifier_log_entry vspec) n 0
    )
    else ()

let ext_evict_val_is_stored_val (#app #n:_) (il: verifiable_log app n) (i: seq_index il):
  Lemma (requires (V.is_evict (I.index il i)))
        (ensures (let tid = I.src il i in
                  let st_pre = thread_store_pre tid il i in
                  let e = I.index il i in
                  let ee = mk_vlog_entry_ext il i in
                  let bk = V.evict_slot e in
                  store_contains st_pre bk /\
                  HV.stored_value st_pre bk = value_ext ee))
  = lemma_cur_thread_state_extend il i

let ext_blum_timestamp_is_src (#app #n:_) (il: verifiable_log app n) (i: seq_index il)
  : Lemma (requires (is_blum_evict il i))
          (ensures (let tid = I.src il i in
                    let EvictBlum _ _ tid_e = mk_vlog_entry_ext il i in
                    tid_e = tid))
  = lemma_cur_thread_state_extend il i

let ext_app_records_is_stored_val
  (#app #n:_)
  (il: verifiable_log app n)
  (i: seq_index il)
  : Lemma (requires (V.is_appfn (I.index il i)))
          (ensures (let open Zeta.GenericVerifier in
                    let App (RunApp f p ss) rs = mk_vlog_entry_ext il i in
                    let vs = cur_thread_state_pre il i in
                    contains_distinct_app_keys vs ss /\
                    rs = reads vs ss))
  = lemma_cur_thread_state_extend il i

let root_never_evicted (#app #n:_) (il: verifiable_log app n) (i: seq_index il)
  : Lemma (requires (V.is_evict (I.index il i)))
          (ensures (let e = I.index il i in
                    let bk = V.evict_slot e in
                    bk <> Zeta.BinTree.Root))
  = lemma_cur_thread_state_extend il i

let root_never_added (#app #n:_) (il: verifiable_log app n) (i: seq_index il):
  Lemma (requires (V.is_add (I.index il i)))
        (ensures (let e = I.index il i in
                  let bk = V.add_slot e in
                  bk <> Zeta.BinTree.Root))
  = lemma_cur_thread_state_extend il i

let app_key_not_ancestor (#app #n:_) (gk: key app) (il: eac_log app n) (i: seq_index il)
  : Lemma (requires (let ki = to_base_key gk in
                     let e = index il i in
                     AppK? gk /\
                     not (e `refs_key` ki)))
          (ensures (let ki = to_base_key gk in
                    let e = index il i in
                    not (e `exp_refs_key` ki)))
  = lemma_cur_thread_state_extend il i

let ev_is_sv_prop
  (#app #n:_)
  (il: eac_log app n)
  (gk: key app {AppK? gk})
  = let es = eac_state_of_genkey gk il in
    EACInStore? es ==>
    (let EACInStore _ _ v = es in
     stored_value gk il = v)

let ev_is_sv_init
  (#app #n:_)
  (il: eac_log app n {length il = 0})
  (gk: key app {AppK? gk})
  : Lemma (ensures (ev_is_sv_prop il gk))
  = eac_state_empty (to_base_key gk)  il

#push-options "--z3rlimit_factor 3"

let ev_is_sv_snoc_nonrefs
  (#app #n:_)
  (il: eac_log app n {length il > 0})
  (gk: key app {AppK? gk})
  : Lemma (requires (let i = length il - 1 in
                     let e = index il i in
                     let k = to_base_key gk in
                     not (e `refs_key` k) /\
                     ev_is_sv_prop (prefix il i) gk))
          (ensures (ev_is_sv_prop il gk))
  = let i = length il - 1 in
    let ki = to_base_key gk in
    let il' = prefix il i in
    let e = index il i in
    let es = eac_state_of_key ki il in
    let es' = eac_state_of_key ki il' in

    if EACInStore? es then (
      eac_state_snoc ki il;
      lemma_cur_thread_state_extend il i;
      SA.lemma_fullprefix_equal il;

      assert(es = es');
      app_key_not_ancestor gk il i;
      assert(not (e `exp_refs_key` ki));
      assert(stored_tid ki il' = src il' (last_idx (HV.is_add_of_key ki) (i_seq il')));
      last_idx_snoc (HV.is_add_of_key ki) (i_seq il);
      assert(stored_tid ki il = stored_tid ki il');
      let t = stored_tid ki il in
      not_refs_implies_store_unchanged ki t il i
    )

let ev_is_sv_snoc_add
  (#app #n:_)
  (il: eac_log app n {length il > 0})
  (gk: key app {AppK? gk})
  : Lemma (requires (let i = length il - 1 in
                     let e = index il i in
                     let k = to_base_key gk in
                     is_add e /\ k = add_slot e /\
                     ev_is_sv_prop (prefix il i) gk))
          (ensures (ev_is_sv_prop il gk))
  = let i = length il - 1 in
    let t = src il i in
    let ki = to_base_key gk in
    let e = index il i in
    let gk2,gv = add_record e in

    eac_state_snoc ki il;
    lemma_cur_thread_state_extend il i;
    SA.lemma_fullprefix_equal il;

    if gk = gk2 then
      key_in_unique_store ki il t (stored_tid ki il)

#pop-options

let ev_is_sv_snoc_evict
  (#app #n:_)
  (il: eac_log app n {length il > 0})
  (gk: key app {AppK? gk})
  : Lemma (requires (let i = length il - 1 in
                     let e = index il i in
                     let k = to_base_key gk in
                     is_evict e /\ k = evict_slot e /\
                     ev_is_sv_prop (prefix il i) gk))
          (ensures (ev_is_sv_prop il gk))
  = let ki = to_base_key gk in
    eac_state_snoc ki il

#push-options "--z3rlimit_factor 3"

let ev_is_sv_snoc_appfn
  (#app #n:_)
  (il: eac_log app n {length il > 0})
  (gk: key app {AppK? gk})
  : Lemma (requires (let i = length il - 1 in
                     let e = index il i in
                     let k = to_base_key gk in
                     RunApp? e /\ e `refs_key` k /\
                     ev_is_sv_prop (prefix il i) gk))
          (ensures (ev_is_sv_prop il gk))
  = let i = length il - 1 in
    let t = src il i in
    let ki = to_base_key gk in
    let e = index il i in
    let RunApp f p ss = e in

    eac_state_snoc ki il;
    lemma_cur_thread_state_extend il i;
    SA.lemma_fullprefix_equal il;

    let idx = index_mem ki ss in
    let fn = appfn f in
    let vs' = thread_state_pre t il i in
    let vs = thread_state_post t il i in

    let rs = reads vs' ss in
    let _,_,ws = fn p rs in
    puts_valid ki e vs' idx;
    assert(HV.stored_value vs.st ki = AppV (S.index ws idx));
    key_in_unique_store ki il t (stored_tid ki il)

#pop-options

let ev_is_sv_snoc
  (#app #n:_)
  (il: eac_log app n {length il > 0})
  (gk: key app {AppK? gk})
  : Lemma (requires (let i = length il - 1 in
                     ev_is_sv_prop (prefix il i) gk))
          (ensures (ev_is_sv_prop il gk))
  = let i = length il - 1 in
    let ki = to_base_key gk in
    let e = index il i in
    if e `refs_key` ki then (
      match e with
      | AddB _ _ _ _
      | AddM _ _ _ -> ev_is_sv_snoc_add il gk
      | EvictBM _ _ _
      | EvictB _ _
      | EvictM _ _ -> ev_is_sv_snoc_evict il gk
      | RunApp _ _ _ -> ev_is_sv_snoc_appfn il gk
    )
    else ev_is_sv_snoc_nonrefs il gk

let rec ev_is_sv
  (#app #n:_)
  (il: eac_log app n)
  (gk: key app {AppK? gk})
  : Lemma (ensures (ev_is_sv_prop il gk))
          (decreases (length il))
  = if length il = 0 then ev_is_sv_init il gk
    else (
      let i = length il - 1 in
      let il' = prefix il i in
      ev_is_sv il' gk;
      ev_is_sv_snoc il gk
    )

let eac_app_state_value_is_stored_value (#app #n:_) (il: eac_log app n) (gk: key app)
  : Lemma (requires (let bk = to_base_key gk in
                     let es = eac_state_of_genkey gk il in
                     AppK? gk /\ EACInStore? es))
          (ensures (let bk = to_base_key gk in
                    let EACInStore _ gk' v = eac_state_of_key bk il in
                    stored_value gk il = v))
  = ev_is_sv il gk

let em_is_sm_prop
  (#app #n:_)
  (il: eac_log app n)
  (k: base_key)
  = let es = eac_state_of_key k il in
    match es with
    | EACInStore m _ _ -> stored_add_method k il = m
    | _ -> true

let em_is_sm_init
  (#app #n:_)
  (il: eac_log app n{length il = 0})
  (k: base_key)
  : Lemma (ensures (em_is_sm_prop il k))
  = eac_state_empty k il

#push-options "--z3rlimit_factor 3"

let em_is_sm_snoc_add
  (#app #n:_)
  (il: eac_log app n{length il > 0})
  (ki: base_key)
  : Lemma (requires (let i = length il - 1 in
                     let e = index il i in
                     let il' = prefix il i in
                     is_add e /\ add_slot e = ki /\
                     em_is_sm_prop il' ki))
          (ensures (em_is_sm_prop il ki))
  = let i = length il - 1 in
    let t = src il i in
    let e = index il i in
    let es = eac_state_of_key ki il in

    eac_state_snoc ki il;
    lemma_cur_thread_state_extend il i;
    SA.lemma_fullprefix_equal il;
    key_in_unique_store ki il t (stored_tid ki il)

#pop-options

let em_is_sm_snoc_evict
  (#app #n:_)
  (il: eac_log app n{length il > 0})
  (ki: base_key)
  : Lemma (requires (let i = length il - 1 in
                     let e = index il i in
                     let il' = prefix il i in
                     is_evict e /\ evict_slot e = ki /\
                     em_is_sm_prop il' ki))
          (ensures (em_is_sm_prop il ki))
  = eac_state_snoc ki il

#push-options "--z3rlimit_factor 4"

let em_is_sm_snoc_appfn
  (#app #n:_)
  (il: eac_log app n{length il > 0})
  (ki: base_key)
  : Lemma (requires (let i = length il - 1 in
                     let e = index il i in
                     let il' = prefix il i in
                     RunApp? e /\ e `refs_key` ki /\
                     em_is_sm_prop il' ki))
          (ensures (em_is_sm_prop il ki))
  = let i = length il - 1 in
    let t = src il i in
    let e = index il i in
    let RunApp f p ss = e in
    let vs_pre = thread_state_pre t il i in
    let vs_post = thread_state_post t il i in
    let il' = prefix il i in

    eac_state_snoc ki il;
    lemma_cur_thread_state_extend il i;
    SA.lemma_fullprefix_equal il;
    runapp_implies_store_contains e vs_pre ki;
    assert(store_contains vs_pre.st ki);
    runapp_doesnot_change_store_keys_extended ki il i;
    assert(add_method_of vs_pre.st ki = add_method_of vs_post.st ki);
    assert(store_contains vs_post.st ki);
    let st = thread_store t il in
    assert(st == vs_post.st);

    key_in_unique_store ki il' t (stored_tid ki il');
    assert(t = stored_tid ki il');

    key_in_unique_store ki il t (stored_tid ki il);
    assert(t = stored_tid ki il);

    ()

#pop-options

#push-options "--z3rlimit_factor 3"

let em_is_sm_snoc_nonrefs
  (#app #n:_)
  (il: eac_log app n{length il > 0})
  (ki: base_key)
  : Lemma (requires (let i = length il - 1 in
                     let e = index il i in
                     let il' = prefix il i in
                     not (e `refs_key` ki) /\
                     em_is_sm_prop il' ki))
          (ensures (em_is_sm_prop il ki))
  = let i = length il - 1 in
    let il' = prefix il i in
    let is' = i_seq il' in
    let e = index il i in
    let es = eac_state_of_key ki il in
    let es' = eac_state_of_key ki il' in
    eac_state_of_root_init il';

    if EACInStore? es then (
      eac_state_snoc ki il;
      lemma_cur_thread_state_extend il i;
      SA.lemma_fullprefix_equal il;

      assert(es = es');
      assert(stored_tid ki il' = src il' (last_idx (HV.is_add_of_key ki) (i_seq il')));
      last_idx_snoc (HV.is_add_of_key ki) (i_seq il);
      assert(stored_tid ki il = stored_tid ki il');
      let t = stored_tid ki il in
      not_refs_implies_store_key_unchanged ki t il i
    )

#pop-options

let em_is_sm_snoc
  (#app #n:_)
  (il: eac_log app n{length il > 0})
  (ki: base_key)
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     em_is_sm_prop il' ki))
          (ensures (em_is_sm_prop il ki))
  = let i = length il - 1 in
    let e = index il i in
    if e `refs_key` ki then (
      match e with
      | AddB _ _ _ _
      | AddM _ _ _ -> em_is_sm_snoc_add il ki
      | EvictBM _ _ _
      | EvictB _ _
      | EvictM _ _ -> em_is_sm_snoc_evict il ki
      | RunApp _ _ _ -> em_is_sm_snoc_appfn il ki
    )
    else em_is_sm_snoc_nonrefs il ki

let rec em_is_sm
  (#app #n:_)
  (il: eac_log app n)
  (ki: base_key)
  : Lemma (ensures (em_is_sm_prop il ki))
          (decreases (length il))
  = if length il = 0 then em_is_sm_init il ki
    else (
      let i = length il - 1  in
      let il' = prefix il i in
      em_is_sm il' ki;
      em_is_sm_snoc il ki
    )

let eac_add_method_is_stored_addm (#app #n:_) (il: eac_log app n) (bk: base_key)
  : Lemma (requires (EACInStore? (eac_state_of_key bk il)))
          (ensures (let EACInStore m _ _ = eac_state_of_key bk il in
                    m = stored_add_method bk il))
  = em_is_sm il bk

(* the state of each key for an empty log is init *)
let init_state_empty (#app #n:_) (il: verifiable_log app n {S.length il = 0}) (bk: base_key):
  Lemma (eac_state_of_key bk il = EACInit)
  = eac_state_empty bk il

let eac_boundary (#app #n:_) (il: neac_log app n)
  : (i: seq_index il{is_eac (prefix il i) /\
                     ~ (is_eac (prefix il (i+1)))})
  = let le = vlog_ext_of_il_log il in
    max_eac_prefix le

let eac_fail_key (#app #n:_) (il: neac_log app n)
  : k:base_key {let i = eac_boundary il in
                let e = I.index il i in
                eac_state_of_key_post k il i = EACFail /\
                eac_state_of_key_pre k il i <> EACFail /\
                e `refs_key` k}
  = let le = vlog_ext_of_il_log il in
    let i = eac_boundary il in
    let k = EAC.eac_fail_key le in
    eac_state_transition k il i;
    lemma_cur_thread_state_extend il i;
    k
