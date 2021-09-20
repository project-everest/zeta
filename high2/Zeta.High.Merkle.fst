module Zeta.High.Merkle

module V = Zeta.GenericVerifier
module HV = Zeta.High.Verifier
module BP = Zeta.BinTreePtr
module M = Zeta.Merkle

let stored_value (#app:_) = HV.stored_value #app

(* three type of edge additions due to AddM (k,_) k' *)
type addm_t=
  | NoNewEdge         (* common case: no new added; k' points k *)
  | NewEdge           (* new edge added: k' points to none along k direction *)
  | CutEdge           (* cut an existing edge: k' points to k2, is_proper_desc k2 k *)

let addm_props
  (#app #n:_)
  (il: verifiable_log app n )
  (i: seq_index il{AddM? (index il i) /\ is_eac (prefix il i)})
  : Lemma (ensures (let AddM (gk, gv) k k' = index il i in
                    let il' = prefix il i in
                    is_proper_desc k k' /\
                    (let v' = eac_merkle_value k' il' in
                     let c = desc_dir k k' in
                     let dh' = desc_hash v' c in
                     match dh' with
                     | Empty -> gv = init_value gk
                     | Desc k2 h2 b2 -> (k2 = k /\ h2 = hashfn gv /\ b2 = false) \/
                                        (is_proper_desc k2 k /\ gv = init_value gk))))
          [SMTPat (index il i)]
  = let il' = prefix il i in
    let AddM _ _ k' = index il i in
    lemma_cur_thread_state_extend il i;
    eac_value_is_stored_value_int il' k' (src il i)

(* the property satisfied by all base keys used as an ancestor in addm/evictm/evictbm *)
let ancestor_es_prop (#app:_)
  (bk: base_key)
  (es: eac_state app bk)
  = bk = Root /\ es = EACInit \/
    bk <> Root /\ EACInStore? es

(* TODO: Migrate to interleave? *)
let store_contains_implies
  (#app #n:_)
  (bk: base_key)
  (il: eac_log app n)
  (t:nat{t < n})
  : Lemma (ensures (let st = thread_store t il in
                    store_contains st bk ==>
                    bk <> Root ==>
                    EACInStore? (eac_state_of_key bk il) /\
                    stored_tid bk il = t))
  = let st = thread_store t il in
    if bk <> Root && store_contains st bk then (
      FStar.Classical.exists_intro (fun tid -> store_contains (thread_store tid il) bk) t;
      lemma_instore bk il;
      key_in_unique_store bk il t (stored_tid bk il)
    )

let addm_es_props
  (#app #n:_)
  (il: verifiable_log app n )
  (i: seq_index il{AddM? (index il i) /\ is_eac (prefix il i)})
  : Lemma (ensures (let AddM _ k k' = index il i in
                    let il' = prefix il i in
                    let es' = eac_state_of_key_pre k' il i in
                    ancestor_es_prop k' es'))
          [SMTPat (index il i)]
  = let il' = prefix il i in
    let AddM _ _ k' = index il i in
    lemma_cur_thread_state_extend il i;
    let es' = eac_state_of_key_pre k' il i in
    store_contains_implies k' il' (src il i);
    if k' = Root then
      eac_state_of_root_init il'

let addm_type
  (#app #n:_)
  (il: verifiable_log app n)
  (i: seq_index il{AddM? (index il i) /\ is_eac (prefix il i)})
  : addm_t
  = let AddM (gk, gv) k k' = index il i in
    let il' = prefix il i in
    let v' = eac_merkle_value k' il' in
    let c = desc_dir k k' in
    let dh' = desc_hash v' c in
    match dh' with
    | Empty -> NewEdge
    | Desc k2 h2 b2 -> if k2 = k then NoNewEdge else CutEdge

let cutedge_desc
  (#app #n:_)
  (il: verifiable_log app n) (i:_{is_eac (prefix il i) /\ addm_type il i = CutEdge})
  = let AddM (gk, gv) k k' = index il i in
    let il' = prefix il i in
    let v' = eac_merkle_value k' il' in
    let c = desc_dir k k' in
    let dh' = desc_hash v' c in
    match dh' with
    | Desc k2 h2 b2 -> k2

let is_merkle_evict (#app:_) (e: vlog_entry app)
  = EvictM? e \/ EvictBM? e

let ancestor_slot (#app) (e:vlog_entry app {is_merkle_evict e})
  = match e with
    | EvictM _ k' -> k'
    | EvictBM _ k' _ -> k'

let evictm_props (#app #n:_) (il: eac_log app n) (i: seq_index il{is_merkle_evict (index il i)})
  : Lemma (ensures (let k = evict_slot (index il i) in
                    let k' = ancestor_slot (index il i) in
                    let il' = prefix il i in
                    is_proper_desc k k' /\
                    (let v' = eac_merkle_value k' il' in
                     let c = desc_dir k k' in
                     points_to v' c k)))
          [SMTPat (index il i)]
  = let il' = prefix il i in
    let k = evict_slot (index il i) in
    let k' = ancestor_slot (index il i) in
    lemma_cur_thread_state_extend il i;
    eac_value_is_stored_value il' (IntK k') (src il i)

let evictm_es_props (#app #n:_) (il: eac_log app n) (i:_ {EvictM? (index il i)})
  : Lemma (ensures (let EvictM k _ = index il i in
                    let es_pre = eac_state_of_key_pre k il i in
                    let es_post = eac_state_of_key_post k il i in
                    EACInStore? es_pre /\ EACEvictedMerkle? es_post))
          [SMTPat (index il i)]
  = let e = index il i in
    let EvictM k _ = e in
    let il' = prefix il i in
    let ee = mk_vlog_entry_ext il i in
    lemma_cur_thread_state_extend il i;
    store_contains_implies k il' (src il i);
    eac_state_transition k il i

let evictbm_es_props (#app #n:_) (il: eac_log app n) (i:_ {EvictBM? (index il i)})
  : Lemma (ensures (let EvictBM k _ _ = index il i in
                    let es_pre = eac_state_of_key_pre k il i in
                    let es_post = eac_state_of_key_post k il i in
                    EACInStore? es_pre /\ EACEvictedBlum? es_post))
          [SMTPat (index il i)]
  = let e = index il i in
    let EvictBM k _ _ = e in
    let il' = prefix il i in
    let ee = mk_vlog_entry_ext il i in
    lemma_cur_thread_state_extend il i;
    store_contains_implies k il' (src il i);
    eac_state_transition k il i

let merkle_evict_ancestor_props
  (#app #n:_)
  (il: eac_log app n) (i:_ {is_merkle_evict (index il i)})
  : Lemma (ensures (let k = ancestor_slot (index il i) in
                    let es_pre = eac_state_of_key_pre k il i in
                    let es_post = eac_state_of_key_post k il i in
                    es_pre = es_post /\ ancestor_es_prop k es_pre))
          [SMTPat (index il i)]
  = let k = ancestor_slot (index il i) in
    let _ = mk_vlog_entry_ext il i in
    let il' = prefix il i in
    lemma_cur_thread_state_extend il i;
    store_contains_implies k il' (src il i);
    eac_state_transition k il i;
    if k = Root then
      eac_state_of_root_init il'

let runapp_refs_only_leafkeys (#app #n:_) (il: eac_log app n) (i:_ {RunApp? (index il i)}) (k: base_key)
  : Lemma (ensures (let e = index il i in
                    e `refs_key` k ==> is_leaf_key k))
  = let e = index il i in
    lemma_cur_thread_state_extend il i;
    let RunApp f p ss = e in
    let vs_pre = thread_state_pre (src il i) il i in
    if e `refs_key` k then
      let idx = index_mem k ss in
      get_record_set_correct ss vs_pre idx

let eac_ptrfn_aux (#app #n:_) (il: eac_log app n) (k:merkle_key) (c:bin_tree_dir)
  : option (base_key)
  = let v = eac_merkle_value k il in
    if M.points_to_none v c
    then None
    else Some (M.pointed_key v c)

let eac_state_transition_snoc
  (#app #n:_)
  (bk: base_key)
  (il: eac_log app n {length il > 0})
  : Lemma (ensures (let i = length il - 1 in
                    let il' = prefix il i in
                    let es' = eac_state_of_key bk il' in
                    let es = eac_state_of_key bk il in
                    let e = index il i in
                    es' <> es ==> (
                    e `refs_key` bk /\
                    (match es', es with
                    | EACInit, EACInStore m _ _ -> AddM? e /\ m = MAdd
                    | EACInStore _ _ _ , EACEvictedBlum _ _ _ _ -> V.is_blum_evict e
                    | EACInStore _ gk1 _ , EACEvictedMerkle gk2 _ -> EvictM? e /\ gk1 = gk2
                    | EACEvictedBlum _ _ _ _, EACInStore m _ _ -> AddB? e /\ m = BAdd
                    | EACEvictedMerkle _ _, EACInStore m _ _ -> AddM? e /\ m = MAdd
                    | EACInStore m1 _ _, EACInStore m2 _ _ -> RunApp? e /\ m1 = m2
                    | _ -> False))))
  = eac_state_snoc bk il

let eac_state_unchanged_snoc
  (#app #n:_)
  (bk: base_key)
  (il: eac_log app n {length il > 0})
  : Lemma (ensures (let i = length il - 1 in
                    let il' = prefix il i in
                    let es' = eac_state_of_key bk il' in
                    let es = eac_state_of_key bk il in
                    let e = index il i in
                    es = es' ==>
                    (e `refs_key` bk) ==>
                    RunApp? e /\ EACInStore? es))
  = eac_state_snoc bk il

#push-options "--z3rlimit_factor 3"

let eac_value_root_snoc
  (#app #n:_)
  (il: eac_log app n {length il > 0})
  : Lemma (ensures (let i = length il - 1 in
                    let e = index il i in
                    let il' = prefix il i in
                    let ev = eac_value (IntK Root) il in
                    let ev' = eac_value (IntK Root) il' in
                    match e with
                    | EvictBM _ k' _
                    | EvictM _ k'
                    | AddM _ _ k' -> if Root <> k' then ev = ev' else True
                    | _ -> ev = ev'))
  = let i = length il - 1 in
    let il' = prefix il i in
    let e = index il i in
    let t = src il i in
    lemma_cur_thread_state_extend il i;
    lemma_root_in_store0 il;
    lemma_root_in_store0 il';
    eac_value_is_stored_value_int il' Root 0;
    eac_value_is_stored_value_int il Root 0;
    lemma_fullprefix_equal il;

    match e with
    | AddM _ _ k'
    | EvictBM _ k' _
    | EvictM _ k' ->
      if Root <> k' then
        if t = 0 then ()
        else
          lemma_non_cur_thread_state_extend 0 il i
    | VerifyEpoch
    | NextEpoch
    | EvictB _ _
    | AddB _ _ _ _ ->
      if t = 0 then ()
      else
        lemma_non_cur_thread_state_extend 0 il i
    | RunApp _ _ _ ->
      runapp_refs_only_leafkeys il i Root;
      not_refs_implies_store_unchanged Root 0 il i

#pop-options

let not_refs_implies_eac_value_unchanged_snoc (#app #n:_)
  (gki: key app)
  (il: eac_log app n{length il > 0})
  : Lemma (ensures (let i = length il - 1 in
                    let e = index il i in
                    let il' = prefix il i in
                    let ev = eac_value gki il in
                    let ev' = eac_value gki il' in
                    let ki = to_base_key gki in
                    not (e `exp_refs_key` ki) ==>
                    ev = ev'))
  = let i = length il - 1 in
    let t = src il i in
    let e = index il i in
    let il' = prefix il i in
    let ev = eac_value gki il in
    let ev' = eac_value gki il' in
    let ki = to_base_key gki in
    let es = eac_state_of_genkey gki il in
    let es' = eac_state_of_genkey gki il' in
    eac_state_snoc ki il;

    if not (e `exp_refs_key` ki) then (
      assert(es = es');
      if ki = Root then
        eac_value_root_snoc il
      else match es with
      | EACInit ->
        eac_value_init_state_is_init il gki;
        eac_value_init_state_is_init il' gki
      | EACInStore m gk v ->
        let t' = stored_tid ki il' in
        not_refs_implies_store_unchanged ki t' il i;
        eac_value_is_stored_value il gki t';
        eac_value_is_stored_value il' gki t'
      | _ ->
        eac_value_is_evicted_value il gki;
        eac_value_is_evicted_value il' gki
    )

let eac_value_snoc_simple_addb
  (#app #n:_)
  (gkf: key app)
  (il: eac_log app n {length il > 0})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     let e = index il i in
                     AddB? e))
          (ensures (let i = length il - 1 in
                    let il' = prefix il i in
                    let e = index il i in
                    let bkf = to_base_key gkf in
                    match e with
                    | AddB (gk,gv) k _ _ -> eac_value gkf il = eac_value gkf il'))
  = let i = length il - 1 in
    let t = src il i in
    let il' = prefix il i in
    let e = index il i in
    let ee = mk_vlog_entry_ext il i in
    let ki = to_base_key gkf in
    let es = eac_state_of_key ki il in
    let es' = eac_state_of_key ki il' in

    not_refs_implies_eac_value_unchanged_snoc gkf il;
    eac_state_snoc ki il;
    lemma_cur_thread_state_extend il i;

    match e with
    | AddB (gk,gv) k _ _ ->
      if k = ki then
        match es', es with
        | EACEvictedBlum gk' gv' _ _, EACInStore _ _ _ ->
          assert(gk' = gk /\ gv = gv');
          if gkf = gk then (
            eac_value_is_evicted_value il' gkf;
            eac_value_is_stored_value il gkf t
          )
          else (
            eac_value_init_state_is_init il gkf;
            eac_value_init_state_is_init il' gkf
          )

let eac_value_snoc_simple_evictm
  (#app #n:_)
  (gki: key app)
  (il: eac_log app n {length il > 0})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     let e = index il i in
                     EvictM? e))
          (ensures (let i = length il - 1 in
                    let il' = prefix il i in
                    let e = index il i in
                    let ki = to_base_key gki in
                    match e with
                    | EvictM k k' -> if k' = ki then
                                       let v' = eac_merkle_value k' il' in
                                       let es = eac_state_of_key k il' in
                                       let gk = to_gen_key es in
                                       let v = eac_value gk il' in
                                       let c = desc_dir k k' in
                                       let v' = update_value v' c k (hashfn v) false in
                                       eac_value gki il = IntV v'
                                     else
                                       eac_value gki il = eac_value gki il'))
  = let i = length il - 1 in
    let t = src il i in
    let il' = prefix il i in
    let e = index il i in
    let ee = mk_vlog_entry_ext il i in
    let ki = to_base_key gki in
    let es = eac_state_of_key ki il in
    let es' = eac_state_of_key ki il' in

    not_refs_implies_eac_value_unchanged_snoc gki il;
    eac_state_snoc ki il;
    lemma_cur_thread_state_extend il i;

    match e with
    | EvictM k k' ->
     if ki = k then (
       match es', es with
       | EACInStore _ gk _, EACEvictedMerkle _ _ ->
         if gk <> gki then (
           eac_value_init_state_is_init il gki;
           eac_value_init_state_is_init il' gki
         )
         else (
           key_in_unique_store ki il' t (stored_tid ki il');
           assert(stored_tid ki il' = t);
           eac_value_is_stored_value il' gki t;
           eac_value_is_evicted_value il gki;
           ext_evict_val_is_stored_val il i
         )
     )
     else if ki = k' then (
       eac_value_is_stored_value_int il' ki t;
       eac_value_is_stored_value_int il ki t;
       store_contains_implies k il' t;
       eac_value_is_stored_value il' (to_gen_key (eac_state_of_key k il')) t
     )

let eac_value_snoc_simple_evictb
  (#app #n:_)
  (gki: key app)
  (il: eac_log app n {length il > 0})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     let e = index il i in
                     EvictB? e))
          (ensures (let i = length il - 1 in
                    let il' = prefix il i in
                    let e = index il i in
                    let ki = to_base_key gki in
                    match e with
                    | EvictB  _ _  -> eac_value gki il = eac_value gki il'))
  = let i = length il - 1 in
    let t = src il i in
    let il' = prefix il i in
    let e = index il i in
    let ee = mk_vlog_entry_ext il i in
    let ki = to_base_key gki in
    let es = eac_state_of_key ki il in
    let es' = eac_state_of_key ki il' in

    not_refs_implies_eac_value_unchanged_snoc gki il;
    eac_state_snoc ki il;
    lemma_cur_thread_state_extend il i;

    match e with
    | EvictB k _ ->
      if k = ki then (
        match es', es with
        | EACInStore _ gk _, EACEvictedBlum _ _ _ _ ->
          if gki = gk then (
            key_in_unique_store ki il' t (stored_tid ki il');
            eac_value_is_stored_value il' gki t;
            eac_value_is_evicted_value il gki;
            ext_evict_val_is_stored_val il i
          )
          else (
            eac_value_init_state_is_init il gki;
            eac_value_init_state_is_init il' gki
          )
      )

#push-options "--z3rlimit_factor 3"

let eac_value_snoc_simple_evictbm
  (#app #n:_)
  (gki: key app)
  (il: eac_log app n {length il > 0})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     let e = index il i in
                     EvictBM? e))
          (ensures (let i = length il - 1 in
                    let il' = prefix il i in
                    let e = index il i in
                    let ki = to_base_key gki in
                    match e with
                    | EvictBM k k' _ -> if k' = ki then
                                       let v' = eac_merkle_value k' il' in
                                       let es = eac_state_of_key k il' in
                                       let gk = to_gen_key es in
                                       let v = eac_value gk il' in
                                       let c = desc_dir k k' in
                                       let dh' = desc_hash v' c in
                                       let Desc k2 h2 b2 = dh' in
                                       let v' = update_value v' c k h2 true in
                                       eac_value gki il = IntV v'
                                     else
                                       eac_value gki il = eac_value gki il'))
  = let i = length il - 1 in
    let t = src il i in
    let il' = prefix il i in
    let e = index il i in
    let ee = mk_vlog_entry_ext il i in
    let ki = to_base_key gki in
    let es = eac_state_of_key ki il in
    let es' = eac_state_of_key ki il' in

    not_refs_implies_eac_value_unchanged_snoc gki il;
    eac_state_snoc ki il;
    lemma_cur_thread_state_extend il i;

    match e with
    | EvictBM k k' _ ->
     if ki = k then (
       match es', es with
       | EACInStore _ gk _, EACEvictedBlum _ _ _ _ ->
         if gk <> gki then (
           eac_value_init_state_is_init il gki;
           eac_value_init_state_is_init il' gki
         )
         else (
           key_in_unique_store ki il' t (stored_tid ki il');
           assert(stored_tid ki il' = t);
           eac_value_is_stored_value il' gki t;
           eac_value_is_evicted_value il gki;
           ext_evict_val_is_stored_val il i
         )
     )
     else if ki = k' then (
       eac_value_is_stored_value_int il' ki t;
       eac_value_is_stored_value_int il ki t;
       store_contains_implies k il' t;
       eac_value_is_stored_value il' (to_gen_key (eac_state_of_key k il')) t;
        ()
     )

#pop-options

let eac_value_snoc_simple
  (#app #n:_)
  (gkf: key app)
  (il: eac_log app n {length il > 0})
  : Lemma (ensures (let i = length il - 1 in
                    let il' = prefix il i in
                    let e = index il i in
                    let bkf = to_base_key gkf in
                    match e with
                    | AddM (gk,gv) k k' -> if bkf <> k && bkf <> k' then
                                             eac_value gkf il = eac_value gkf il'
                                           else True
                    | AddB _ _ _ _ -> eac_value gkf il = eac_value gkf il'
                    | EvictM k k' -> if k' = bkf then
                                       let v' = eac_merkle_value k' il' in
                                       let es = eac_state_of_key k il' in
                                       let gk = to_gen_key es in
                                       let v = eac_value gk il' in
                                       let c = desc_dir k k' in
                                       let v' = update_value v' c k (hashfn v) false in
                                       eac_value gkf il = IntV v'
                                     else
                                       eac_value gkf il = eac_value gkf il'
                    | EvictB _ _ -> eac_value gkf il = eac_value gkf il'
                    | EvictBM k k' _ -> if k' = bkf then
                                       let v' = eac_merkle_value k' il' in
                                       let es = eac_state_of_key k il' in
                                       let gk = to_gen_key es in
                                       let v = eac_value gk il' in
                                       let c = desc_dir k k' in
                                       let dh' = desc_hash v' c in
                                       let Desc k2 h2 b2 = dh' in
                                       let v' = update_value v' c k h2 true in
                                       eac_value gkf il = IntV v'
                                     else
                                       eac_value gkf il = eac_value gkf il'
                    | VerifyEpoch -> eac_value gkf il = eac_value gkf il'
                    | NextEpoch -> eac_value gkf il = eac_value gkf il'
                    | RunApp _ _ _ -> if e `refs_key` bkf then
                                        True
                                      else
                                       eac_value gkf il = eac_value gkf il'
  ))
  = let i = length il - 1 in
    let il' = prefix il i in
    let e = index il i in
    let bkf = to_base_key gkf in
    let es = eac_state_of_key bkf il in
    let es' = eac_state_of_key bkf il' in
    eac_state_snoc bkf il;
    lemma_cur_thread_state_extend il i;
    not_refs_implies_eac_value_unchanged_snoc gkf il;

    match e with
    | AddB _ _ _ _ -> eac_value_snoc_simple_addb gkf il
    | EvictM _ _ -> eac_value_snoc_simple_evictm gkf il
    | EvictB _ _ -> eac_value_snoc_simple_evictb gkf il
    | EvictBM _ _ _ -> eac_value_snoc_simple_evictbm gkf il
    | _ -> ()


let empty_or_points_to_desc
  (#app #n:_)
  (il: eac_log app n)
  (k:merkle_key)
  (c:bin_tree_dir)
  = match eac_ptrfn_aux il k c with
    | None -> true
    | Some k2 -> is_desc k2 (child c k)


#push-options "--z3rlimit_factor 3"

let eac_ptrfn_empty_or_points_desc_addm_extend
  (#app #n:_)
  (il: eac_log app n {length il > 0})
  (ki: merkle_key)
  (c: bin_tree_dir)
  : Lemma (requires (let i = length il - 1 in
                     let e = index il i in
                     let il' = prefix il i in
                     AddM? e /\
                     empty_or_points_to_desc il' ki c))
          (ensures (empty_or_points_to_desc il ki c))
  = let i = length il - 1 in
    let e = index il i in
    let il' = prefix il i in
    let es = eac_state_of_key ki il in
    let es' = eac_state_of_key ki il' in
    let AddM (gk,gv) k k' = e in
    let t = src il i in

    eac_value_snoc_simple (IntK ki) il;
    lemma_cur_thread_state_extend il i;
    eac_state_snoc ki il;

    if ki = k then (
      match es', es with
      | EACInit, EACInStore _ _ _ ->
        store_contains_implies ki il t;
        eac_value_is_stored_value il (IntK ki) t
      | EACEvictedMerkle _ _, EACInStore _ _ _ ->
        store_contains_implies ki il t;
        eac_value_is_stored_value il (IntK ki) t;
        eac_value_is_evicted_value il' (IntK ki)
    )
    else if ki = k' then (
      store_contains_implies ki il t;
      store_contains_implies ki il' t;
      eac_value_is_stored_value il' (IntK ki) t;
      eac_value_is_stored_value il (IntK ki) t
    )

#pop-options

let rec eac_ptrfn_empty_or_points_to_desc
  (#app #n:_)
  (il: eac_log app n)
  (k: merkle_key)
  (c: bin_tree_dir)
  : Lemma (ensures (empty_or_points_to_desc il k c))
          (decreases (length il))
  = if length il = 0 then
      eac_value_init (IntK k) il
    else
      let i = length il - 1  in
      let il' = prefix il i in
      let e = index il i in
      eac_ptrfn_empty_or_points_to_desc il' k c;
      eac_value_snoc_simple (IntK k) il;
      match e with
      | AddM _ _ _ -> eac_ptrfn_empty_or_points_desc_addm_extend il k c
      | RunApp _ _ _ -> runapp_refs_only_leafkeys il i k
      | _ -> ()

let eac_ptrfn_base
  (#app #n:_)
  (il: eac_log app n)
  (k: bin_tree_node)
  (c: bin_tree_dir)
  : o:(option bin_tree_node){None = o \/ is_desc (Some?.v o) (child c k)}
  = if depth k >= key_size then None
    else
      let or = eac_ptrfn_aux il k c in
      eac_ptrfn_empty_or_points_to_desc il k c;
      if or = None then None
      else Some (Some?.v or)

(* eac pointer function *)
let eac_ptrfn
  (#app #n:_)
  (il: eac_log app n): ptrfn =
  eac_ptrfn_base il

(* eac_ptrfn value is the same as the eac_value *)
let lemma_eac_ptrfn
  (#app #n:_)
  (il: eac_log app n) (k: merkle_key) (c:bin_tree_dir) :
  Lemma (ensures (let pf = eac_ptrfn il in
                  let mv = eac_merkle_value k il in
                  points_to_none mv c /\ pf k c = None \/
                  points_to_some mv c /\ is_desc (pointed_key mv c) (child c k) /\
                  pf k c = Some (pointed_key mv c)))
        [SMTPat (pointed_key (eac_merkle_value k il) c)]
  = let mv = eac_merkle_value k il in
    if points_to_some mv c then
      eac_ptrfn_empty_or_points_to_desc il k c

let eac_ptrfn_snoc_non_ancestor
  (#app #n:_)
  (il: eac_log app n {length il > 0})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     let e = index il i in
                     not (involves_ancestor e)))
          (ensures (let i = length il - 1 in
                    let il' = prefix il i in
                    let pf = eac_ptrfn il in
                    let pf' = eac_ptrfn il' in
                    pf == pf'))
  = let i = length il - 1 in
    let il' = prefix il i in
    let pf = eac_ptrfn il in
    let pf' = eac_ptrfn il' in
    let aux (n c:_)
      : Lemma (ensures (pf n c == pf' n c))
      = if depth n < key_size then (
          lemma_eac_ptrfn il n c;
          lemma_eac_ptrfn il' n c;
          eac_value_snoc_simple (IntK n) il;
          if RunApp? (index il i) then
            runapp_refs_only_leafkeys il i n
        )
    in
    FStar.Classical.forall_intro_2 aux;
    assert(feq_ptrfn pf pf')

let eac_ptrfn_snoc_addm_nonewedge
  (#app #n:_)
  (il: eac_log app n {length il > 0})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     let e = index il i in
                     AddM? e /\ addm_type il i = NoNewEdge))
          (ensures (let i = length il - 1 in
                    let il' = prefix il i in
                    let pf = eac_ptrfn il in
                    let pf' = eac_ptrfn il' in
                    pf == pf'))
  = let i = length il - 1 in
    let il' = prefix il i in
    let pf = eac_ptrfn il in
    let pf' = eac_ptrfn il' in
    let t = src il i in
    let AddM (gk,gv) k k' = index il i in
    lemma_cur_thread_state_extend il i;
    lemma_fullprefix_equal il;
    eac_value_is_stored_value il' (IntK k') t;

    let aux (ki c:_)
      : Lemma (ensures (pf ki c == pf' ki c))
      = if depth ki < key_size then (
          lemma_eac_ptrfn il ki c;
          lemma_eac_ptrfn il' ki c;
          if ki = k then (
            let es' = eac_state_of_key ki il' in
            let es = eac_state_of_key ki il in
            eac_state_snoc ki il;
            match es', es with
            | EACInit, EACInStore _ _ _ ->
              eac_value_init_state_is_init il' (IntK k);
              eac_value_is_stored_value il (IntK k) (src il i)
            | EACEvictedMerkle _ _, EACInStore _ _ _ ->
              eac_value_is_evicted_value il' (IntK k);
              eac_value_is_stored_value il (IntK k) (src il i)
          )
          else if ki = k' then
            eac_value_is_stored_value il (IntK k') t
          else
            eac_value_snoc_simple (IntK ki) il
        )
    in
    FStar.Classical.forall_intro_2 aux;
    assert(feq_ptrfn pf pf')

let eac_ptrfn_snoc_addm_newedge
  (#app #n:_)
  (il: eac_log app n {length il > 0})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     let e = index il i in
                     AddM? e /\ addm_type il i = NewEdge))
          (ensures (let i = length il - 1 in
                    let il' = prefix il i in
                    let AddM _ k k' = index il i in
                    let c = desc_dir k k' in
                    let pf = eac_ptrfn il in
                    let pf' = eac_ptrfn il' in
                    not (BP.points_to_some pf' k' c) /\
                    BP.points_to_none pf' k /\
                    pf == extend_ptrfn pf' k k'))
  = let i = length il - 1 in
    let il' = prefix il i in
    let pf = eac_ptrfn il in
    let pf' = eac_ptrfn il' in
    let t = src il i in
    let AddM (gk,gv) k k' = index il i in
    let c = desc_dir k k' in
    lemma_cur_thread_state_extend il i;
    lemma_fullprefix_equal il;
    eac_value_is_stored_value il' (IntK k') t;

    let aux1 ()
      : Lemma (ensures (BP.points_to_none pf' k))
      = if depth k < key_size then (
          let es' = eac_state_of_key k il' in
          eac_state_snoc k il;
          match es' with
          | EACInit ->
            eac_value_init_state_is_init il' (IntK k)

          | EACEvictedMerkle _ _  ->
            eac_value_is_evicted_value il' (IntK k)
        )
    in
    aux1();
    let pfe = extend_ptrfn pf' k k' in
    let aux (ki c:_)
      : Lemma (ensures (pf ki c == pfe ki c))
      = if depth ki < key_size then (
          lemma_eac_ptrfn il ki c;
          lemma_eac_ptrfn il' ki c;
          if ki = k then
            eac_value_is_stored_value il (IntK k) t
          else if ki = k' then
            eac_value_is_stored_value il (IntK k') t
          else
            eac_value_snoc_simple (IntK ki) il
        )
    in
    FStar.Classical.forall_intro_2 aux;
    assert(feq_ptrfn pf pfe)

let eac_ptrfn_snoc_addm_cutedge
  (#app #n:_)
  (il: eac_log app n {length il > 0})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     let e = index il i in
                     AddM? e /\ addm_type il i = CutEdge))
          (ensures (let i = length il - 1 in
                    let il' = prefix il i in
                    let AddM _ k k' = index il i in
                    let c = desc_dir k k' in
                    let pf = eac_ptrfn il in
                    let pf' = eac_ptrfn il' in
                    BP.points_to_none pf' k /\
                    BP.points_to_some pf' k' c /\
                    is_proper_desc (BP.pointed_node pf' k' c) k /\
                    pf == extendcut_ptrfn pf' k k'))
  = let i = length il - 1 in
    let il' = prefix il i in
    let pf = eac_ptrfn il in
    let pf' = eac_ptrfn il' in
    let t = src il i in
    let AddM (gk,gv) k k' = index il i in
    let c = desc_dir k k' in
    lemma_cur_thread_state_extend il i;
    lemma_fullprefix_equal il;
    eac_value_is_stored_value il' (IntK k') t;

    let aux1 ()
      : Lemma (ensures (BP.points_to_none pf' k))
      = if depth k < key_size then (
          let es' = eac_state_of_key k il' in
          eac_state_snoc k il;
          match es' with
          | EACInit ->
            eac_value_init_state_is_init il' (IntK k)

          | EACEvictedMerkle _ _  ->
            eac_value_is_evicted_value il' (IntK k)
        )
    in
    aux1();
    let pfe = extendcut_ptrfn pf' k k' in

    let aux (ki c:_)
      : Lemma (ensures (pf ki c == pfe ki c))
      = if depth ki < key_size then (
          lemma_eac_ptrfn il ki c;
          lemma_eac_ptrfn il' ki c;
          if ki = k then (
            eac_value_is_stored_value il (IntK k) t;
            admit()
          )
          else if ki = k' then (
            eac_value_is_stored_value il (IntK k') t;
            admit()
          )
          else
          admit()
        )
    in
    FStar.Classical.forall_intro_2 aux;
    assert(feq_ptrfn pf pfe)

let eac_ptrfn_snoc
  (#app #n:_)
  (il: eac_log app n {length il > 0})
  : Lemma (ensures (let i = length il - 1 in
                    let il' = prefix il i in
                    let pf = eac_ptrfn il in
                    let pf' = eac_ptrfn il' in
                    let e = index il i in
                    match e with
                    | AddM _ k k' -> (
                      let c = desc_dir k k' in
                      match (addm_type il i) with
                      | NoNewEdge -> pf == pf'
                      | NewEdge ->  not (BP.points_to_some pf' k' c) /\
                                    BP.points_to_none pf' k /\
                                    pf == extend_ptrfn pf' k k'
                      | CutEdge -> BP.points_to_none pf' k /\
                                   BP.points_to_some pf' k' c /\
                                   is_proper_desc (BP.pointed_node pf' k' c) k /\
                                   pf == extendcut_ptrfn pf' k k'
                      )
                    | _ -> feq_ptrfn pf pf'))
  = admit()

let root_reachable (#app #n:_) (il: eac_log app n) (k:base_key)
  : bool
  = let pf = eac_ptrfn il in
    BP.root_reachable pf k

let not_init_equiv_root_reachable (#app #n:_) (il: eac_log app n) (k: base_key)
  = k <> Root ==>
    ((eac_state_of_key k il <> EACInit) <==> root_reachable il k)

let rec lemma_not_init_equiv_root_reachable
  (#app #n:_)
  (il: eac_log app n)
  (k: base_key)
  : Lemma (ensures (not_init_equiv_root_reachable il k))
          (decreases length il)
  = let es = eac_state_of_key k il in
    let pf = eac_ptrfn il in
    if k = Root then ()
    else if length il = 0 then (
      eac_state_empty k il;
      eac_value_init (IntK Root) il;

      lemma_root_is_univ_ancestor k;
      let c = desc_dir k Root in

      assert(None = pf Root c);
      lemma_non_reachable_desc_of_none pf k Root
    )
    else (
      let i = length il - 1 in
      let il' = prefix il i in
      let pf' = eac_ptrfn il' in
      let e = index il i in
      let es' = eac_state_of_key k il' in
      let es = eac_state_of_key k il in

      eac_state_unchanged_snoc k il;
      eac_state_transition_snoc k il;
      eac_ptrfn_snoc il;
      lemma_not_init_equiv_root_reachable il' k;

      match e with
      | AddM _ _ _ ->
        let add_type = addm_type il i in
        (
        match add_type with
        | NoNewEdge -> admit()
        | NewEdge -> admit()
        | CutEdge -> admit()
        )
      | _ -> ()
    )

let lemma_eac_instore_implies_root_reachable
  (#app #n:_)
  (il: eac_log app n)
  (k: base_key)
  : Lemma (ensures (EACInStore? (eac_state_of_key k il) ==> root_reachable il k))
  = let pf = eac_ptrfn il in
    if k = Root
      then lemma_reachable_reflexive pf Root
    else
      lemma_not_init_equiv_root_reachable il k

let eac_ptrfn_rooted (#app #n:_) (il: eac_log app n)
  : Lemma (ensures (rooted (eac_ptrfn il)))
          [SMTPat (eac_ptrfn il)]
  = admit()

(* the ancestor who holds the proof of the value of key k *)
let proving_ancestor (#app #n:_) (il: eac_log app n) (k:base_key{k <> Root}):
  k':base_key{is_proper_desc k k'}
  = let pf = eac_ptrfn il in
    if BP.root_reachable pf k then
      prev_in_path pf k Root
    else
      let k' = first_root_reachable_ancestor pf k in
      assert(is_proper_desc k k');
      k'

let lemma_proving_ancestor_greatest_depth
  (#app #n:_)
  (il: eac_log app n)
  (k:base_key{k <> Root})
  (k2: base_key{is_proper_desc k k2}):
  Lemma (requires (root_reachable il k2))
        (ensures  (let k' = proving_ancestor il k in
                   depth k2 <= depth k')) =
  let k' = proving_ancestor il k in
  let pf = eac_ptrfn il in
  if root_reachable il k then (
    assert(k' = prev_in_path pf k Root);

    lemma_two_ancestors_related k k' k2;
    if is_desc k2 k' then (

      if k2 = k' then ()
      else
        lemma_desc_of_prev_not_reachable pf k Root k2
    )
    else
      lemma_desc_depth_monotonic k' k2
  )
  else lemma_first_root_reachable_ancestor_greatest_depth pf k k2

(* after the first add the proving ancestor always points to self *)
let lemma_proving_ancestor_points_to_self (#app #n:_) (il: eac_log app n) (k:base_key{k <> Root}):
  Lemma (requires (eac_state_of_key k il <> EACInit))
        (ensures (let pk = proving_ancestor il k in
                  let d = desc_dir k pk in
                  let v = eac_merkle_value pk il in
                  points_to v d k))
  = lemma_not_init_equiv_root_reachable il k

(* before the first add the proving ancestor points to none or to a key that is not an ancestor *)
let lemma_proving_ancestor_initial (#app #n:_) (il: eac_log app n) (k:base_key{k <> Root}):
  Lemma (requires (eac_state_of_key k il = EACInit))
        (ensures (let k' = proving_ancestor il k in
                  let v' = eac_merkle_value k' il in
                  let c = desc_dir k k' in
                  points_to_none v' c \/
                  not (is_desc k (pointed_key v' c))))
  = let pf = eac_ptrfn il in
    let k' = proving_ancestor il k in
    let v' = eac_merkle_value k' il in
    let c = desc_dir k k' in
    lemma_not_init_equiv_root_reachable il k;

    if points_to_some v' c then
      let k2 = pointed_key v' c in
      if is_desc k k2 then (
        (* since pf is rooted, points_to implies k2 is root reachable, so k2 <> k *)
        assert(BP.points_to pf k2 k');
        assert(is_proper_desc k k2);
        lemma_proving_ancestor_greatest_depth il k k2
      )

(* initially root is the proving ancestor for all keys *)
let lemma_proving_ancestor_empty (#app #n:_) (il: eac_log app n {length il = 0}) (k: base_key {k <> Root})
  : Lemma (ensures (proving_ancestor il k = Root))
  = admit()

let lemma_proving_ancestor_snoc (#app #n:_) (il: eac_log app n {length il > 0}) (ki: base_key {ki <> Root})
  : Lemma (ensures (let i = length il - 1 in
                    let pf = eac_ptrfn il in
                    let il' = prefix il i in
                    let pf' = eac_ptrfn il' in
                    let e = index il i in
                    match e with
                    | AddM _ k k' ->
                      let am = addm_type il i in
                      (match am with
                       | NewEdge ->
                         if is_proper_desc ki k then
                           proving_ancestor il ki = k
                         else
                           proving_ancestor il ki = proving_ancestor il' ki
                       | CutEdge ->
                         if ki = cutedge_desc il i then
                           proving_ancestor il ki = k
                         else
                           proving_ancestor il ki = proving_ancestor il' ki
                       | _ -> proving_ancestor il ki = proving_ancestor il' ki
                      )
                    | _ -> proving_ancestor il ki = proving_ancestor il' ki))
  = admit()

(* if a key pk points to key k, then pk is the proving ancestor of k; (inverse of
 * lemma_proving_ancestor_points_to_self *)
let lemma_points_to_implies_proving_ancestor
  (#app #n:_)
  (il: eac_log app n)
  (k:base_key)
  (k':merkle_key)
  (d:bin_tree_dir):
  Lemma (requires (let mv = eac_merkle_value k' il in
                   points_to mv d k))
        (ensures (k <> Root /\ proving_ancestor il k = k'))
  = let pf = eac_ptrfn il in
    assert(BP.points_to pf k k');
    lemma_points_to_is_prev pf k Root k'


let lemma_evictm_ancestor_is_proving
  (#app #n:_)
  (il: eac_log app n)
  (i:_{is_merkle_evict (index il i)})
  : Lemma (ensures (let e = index il i in
                    let k' = ancestor_slot e in
                    let k = evict_slot e in
                    let il' = prefix il i in
                    k' = proving_ancestor il' k))
          [SMTPat (index il i)]
  = let il' = prefix il i in
    let e = index il i in
    let k' = ancestor_slot e in
    let k = evict_slot e in
    let c = desc_dir k k' in
    lemma_points_to_implies_proving_ancestor il' k k' c

let proving_ancestor_has_hash (#app #n:_) (il: eac_log app n) (gk:key app{gk <> IntK Root})
  = let k = to_base_key gk in
    let es = eac_state_of_key k il in
    let pk = proving_ancestor il k in
    let mv = eac_merkle_value pk il in
    let c = desc_dir k pk in
    let v = eac_value gk il in
    EACEvictedMerkle? es ==>
    EACEvictedMerkle?.gk es = gk ==>
    pointed_hash mv c = hashfn v

let eac_value_snoc
  (#app #n:_)
  (gkf: key app)
  (il: eac_log app n {length il > 0})
  : Lemma (ensures (let i = length il - 1 in
                    let il' = prefix il i in
                    let e = index il i in
                    let bkf = to_base_key gkf in
                    match e with
                    | AddM (gk,gv) k k' -> (
                      let c = desc_dir k k' in
                      match (addm_type il i) with
                      | NoNewEdge -> eac_value gkf il = eac_value gkf il'
                      | NewEdge -> if k' = bkf then
                                     let v' = eac_merkle_value k' il' in
                                     let v' = update_value v' c k Zeta.Hash.zero false in
                                     eac_value gkf il = IntV v'
                                   else if k = bkf then
                                     eac_value gkf il = init_value gkf
                                   else
                                     eac_value gkf il = eac_value gkf il'
                      | CutEdge -> if k = bkf then
                                     let v = eac_merkle_value k il' in
                                     let v' = eac_merkle_value k' il' in
                                     let Desc k2 h2 b2 = desc_hash v' c in
                                     let c2 = desc_dir k2 k in
                                     let v = update_value v c2 k2 h2 b2 in
                                     eac_value gkf il = IntV v
                                   else if k' = bkf then
                                     let v' = eac_merkle_value k' il' in
                                     let v' = update_value v' c k Zeta.Hash.zero false in
                                     eac_value gkf il = IntV v'
                                   else
                                     eac_value gkf il = eac_value gkf il'
                      )
                    | AddB _ _ _ _ -> eac_value gkf il = eac_value gkf il'
                    | EvictM k k' -> if k' = bkf then
                                       let v' = eac_merkle_value k' il' in
                                       let gk = to_gen_key (eac_state_of_key k il') in
                                       let v = eac_value gk il' in
                                       let c = desc_dir k k' in
                                       let v' = update_value v' c k (hashfn v) false in
                                       eac_value gkf il = IntV v'
                                     else
                                       eac_value gkf il = eac_value gkf il'
                    | EvictB _ _ -> eac_value gkf il = eac_value gkf il'
                    | EvictBM k k' _ -> if k' = bkf then
                                       let v' = eac_merkle_value k' il' in
                                       let es = eac_state_of_key k il' in
                                       let gk = to_gen_key es in
                                       let v = eac_value gk il' in
                                       let c = desc_dir k k' in
                                       let dh' = desc_hash v' c in
                                       let Desc k2 h2 b2 = dh' in
                                       let v' = update_value v' c k h2 true in
                                       eac_value gkf il = IntV v'
                                     else
                                       eac_value gkf il = eac_value gkf il'
                    | VerifyEpoch -> eac_value gkf il = eac_value gkf il'
                    | NextEpoch -> eac_value gkf il = eac_value gkf il'
                    | RunApp _ _ _ -> if e `refs_key` bkf then
                                        True
                                      else
                                       eac_value gkf il = eac_value gkf il'
  ))
  = let i = length il - 1 in
    let il' = prefix il i in
    let e = index il i in
    let bkf = to_base_key gkf in
    eac_value_snoc_simple gkf il;
    match e with
    | AddM _ _ _ -> admit()
    | _ -> ()

let lemma_proving_ancestor_has_hash_addm_newedge_extend
  (#app #n:_)
  (il: eac_log app n{length il > 0})
  (gki: key app {gki <> IntK Root})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     AddM? (index il i) /\
                     addm_type il i = NewEdge /\
                     proving_ancestor_has_hash il' gki))
          (ensures (proving_ancestor_has_hash il gki))
  = let bk = to_base_key gki in
    let es = eac_state_of_key bk il in
    let i = length il - 1 in


    let il' = prefix il i in
    let pk' = proving_ancestor il' bk in
    let pf' = eac_ptrfn il' in

    let AddM (gk,gv) k k' = index il i in
    let c = desc_dir k k' in
    let v' = eac_merkle_value k' il' in
    let dh' = desc_hash v' c in

    eac_state_unchanged_snoc bk il;
    eac_state_transition_snoc bk il;
    eac_value_snoc gki il;
    lemma_proving_ancestor_snoc il bk;

    if EACEvictedMerkle? es then (
      (* neither k or k' have EACEvictedMerkle state *)
      assert(k <> bk);
      assert(k' <> bk);

      assert(points_to_none v' c);
      assert(not (BP.points_to_some pf' k' c));

      lemma_not_init_equiv_root_reachable il' bk;
      assert(root_reachable il' bk);

      let aux()
        : Lemma (ensures (root_reachable il' k'))
        = if k' = Root then lemma_reachable_reflexive pf' Root
          else lemma_eac_instore_implies_root_reachable il' k'
      in
      aux();

      let aux()
        : Lemma (ensures (not (is_desc bk (child c k'))))
        = if is_desc bk (child c k') then
            lemma_reachable_between pf' bk k'
      in
      aux();

      let aux ()
        : Lemma (ensures (not (is_proper_desc bk k)))
        = if is_desc bk k then
            lemma_desc_transitive bk k (child c k')
      in
      aux();

      assert(pk' = proving_ancestor il bk);
      eac_value_snoc (IntK pk') il
    )

let lemma_proving_ancestor_has_hash_addm_cutedge_extend
  (#app #n:_)
  (il: eac_log app n{length il > 0})
  (gki: key app {gki <> IntK Root})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     AddM? (index il i) /\
                     addm_type il i = CutEdge /\
                     proving_ancestor_has_hash il' gki))
          (ensures (proving_ancestor_has_hash il gki))
  = let bk = to_base_key gki in
    let es = eac_state_of_key bk il in
    let i = length il - 1 in


    let il' = prefix il i in
    let pk' = proving_ancestor il' bk in
    let pf' = eac_ptrfn il' in

    let AddM (gk,gv) k k' = index il i in
    let c = desc_dir k k' in
    let v' = eac_merkle_value k' il' in
    let dh' = desc_hash v' c in

    eac_state_unchanged_snoc bk il;
    eac_state_transition_snoc bk il;
    eac_value_snoc gki il;
    lemma_proving_ancestor_snoc il bk;

    if EACEvictedMerkle? es then (
      (* neither k or k' have EACEvictedMerkle state *)
      assert(k <> bk);
      assert(k' <> bk);

      if bk = cutedge_desc il i then (
        eac_value_snoc (IntK k) il;
        lemma_eac_ptrfn il' k' c;
        lemma_points_to_implies_proving_ancestor il' bk k' c
      )
      else
        //assert(pk' = proving_ancestor il bk);
        eac_value_snoc (IntK pk') il
    )

let lemma_proving_ancestor_has_hash_addm_extend
  (#app #n:_)
  (il: eac_log app n{length il > 0})
  (gki: key app {gki <> IntK Root})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     AddM? (index il i) /\
                     proving_ancestor_has_hash il' gki))
          (ensures (proving_ancestor_has_hash il gki))
  = let bk = to_base_key gki in
    let es = eac_state_of_key bk il in
    let i = length il - 1 in
    let il' = prefix il i in
    let am = addm_type il i in
    eac_state_unchanged_snoc bk il;
    eac_state_transition_snoc bk il;
    eac_value_snoc gki il;
    lemma_proving_ancestor_snoc il bk;
    let pk' = proving_ancestor il' bk in

      match am with
      | NoNewEdge ->
        if EACEvictedMerkle? es then eac_value_snoc (IntK pk') il
      | NewEdge -> lemma_proving_ancestor_has_hash_addm_newedge_extend il gki
      | CutEdge -> lemma_proving_ancestor_has_hash_addm_cutedge_extend il gki

let rec lemma_proving_ancestor_has_hash_aux (#app #n:_) (il: eac_log app n) (gk:key app{gk <> IntK Root}):
  Lemma (ensures proving_ancestor_has_hash il gk)
        (decreases (length il))
  = let bk = to_base_key gk in
    let es = eac_state_of_key bk il in
    if length il = 0 then
      eac_state_empty bk il
    else (
      let i = length il - 1 in
      let e = index il i in
      let il' = prefix il i in
      let pk' = proving_ancestor il' bk in
      lemma_proving_ancestor_has_hash_aux il' gk;
      lemma_proving_ancestor_snoc il bk;
      eac_value_snoc gk il;
      eac_state_transition_snoc bk il;
      eac_state_unchanged_snoc bk il;
      eac_value_snoc (IntK pk') il;
      match e with
      | AddM _ _ _ -> lemma_proving_ancestor_has_hash_addm_extend il gk
      | RunApp _ _ _ ->
        runapp_refs_only_leafkeys il i pk'
      | _ -> ()
    )

(* when evicted as merkle the proving ancestor contains our hash *)
let lemma_proving_ancestor_has_hash (#app #n:_) (il: eac_log app n) (gk:key app{gk <> IntK Root}):
  Lemma (requires (let k = to_base_key gk in
                   EACEvictedMerkle? (eac_state_of_key k il) /\
                   EACEvictedMerkle?.gk (eac_state_of_key k il) = gk))
        (ensures (let k = to_base_key gk in
                  let pk = proving_ancestor il k in
                  let mv = eac_merkle_value pk il in
                  let c = desc_dir k pk in
                  let v = HI.eac_value gk il in
                  pointed_hash mv c = hashfn v))
  = lemma_proving_ancestor_has_hash_aux il gk


let lemma_addm_ancestor_is_proving_nonewedge (#app #n:_) (il: verifiable_log app n {length il > 0}):
  Lemma (requires (let n = length il in
                   let il' = I.prefix il (n-1) in
                   let e = I.index il (n-1) in
                   is_eac il' /\ AddM? e /\ addm_type il (n-1) = NoNewEdge))
        (ensures (let n = length il in
                  let e = I.index il (n - 1) in
                  let il' = I.prefix il (n - 1) in
                  let AddM _ k k' = e in
                  Root <> k /\ k' = proving_ancestor il' k))
  = let i = length il - 1 in
    let il' = prefix il i in
    let AddM _ k k' = index il i in
    let c = desc_dir k k' in
    lemma_points_to_implies_proving_ancestor il' k k' c

let lemma_addm_ancestor_is_proving_newedge
  (#app #n:_)
  (il: verifiable_log app n {length il > 0}):
  Lemma (requires (let n = length il in
                   let il' = I.prefix il (n-1) in
                   let e = I.index il (n-1) in
                   is_eac il' /\ AddM? e /\ addm_type il (n-1) = NewEdge))
        (ensures (let n = length il in
                  let e = I.index il (n - 1) in
                  let il' = I.prefix il (n - 1) in
                  let AddM _ k k' = e in
                  Root <> k /\ k' = proving_ancestor il' k))
  = let i = length il - 1 in
    let il' = prefix il i in
    let AddM _ k k' = index il i in
    let c = desc_dir k k' in
    let pf = eac_ptrfn il' in
    assert(pf k' c = None);
    let pk = proving_ancestor il' k in
    let es = eac_state_of_key k il' in

    let aux()
      : Lemma (root_reachable il' k')
      =  if k' = Root then lemma_reachable_reflexive pf Root
          else lemma_eac_instore_implies_root_reachable il' k'
    in
    aux();

    lemma_not_init_equiv_root_reachable il' k;
    if pk <> k' then

      if es = EACInit then (
        (* k is not root reachable since it is in EACInit *)
        assert(not (root_reachable il' k));

        assert(pk = first_root_reachable_ancestor pf k);

        (* by construction pk is the ancestor with the greatest depth *)
        lemma_first_root_reachable_ancestor_greatest_depth pf k k';
        assert(depth k' <= depth pk);

        let aux(): Lemma (is_proper_desc pk k')
          = lemma_two_ancestors_related k k' pk;
            if is_desc k' pk then
              lemma_proper_desc_depth_monotonic k' pk
        in
        aux();
        lemma_two_related_desc_same_dir k pk k';
        lemma_reachable_between pf pk k'
      )
      else
        (* k is root reachable since it is not EACInit *)
        //assert(root_reachable il' k);

        lemma_reachable_between pf k k'

let lemma_addm_ancestor_is_proving_cutedge
  (#app #n:_)
  (il: verifiable_log app n {length il > 0}):
  Lemma (requires (let n = length il in
                   let il' = I.prefix il (n-1) in
                   let e = I.index il (n-1) in
                   is_eac il' /\ AddM? e /\ addm_type il (n-1) = CutEdge))
        (ensures (let n = length il in
                  let e = I.index il (n - 1) in
                  let il' = I.prefix il (n - 1) in
                  let AddM _ k k' = e in
                  Root <> k /\ k' = proving_ancestor il' k))
  = let i = length il - 1 in
    let il' = prefix il i in
    let AddM _ k k' = index il i in
    let c = desc_dir k k' in
    let pf = eac_ptrfn il' in
    let pk = proving_ancestor il' k in
    let es = eac_state_of_key k il' in
    let k2 = cutedge_desc il i in
    lemma_eac_ptrfn il' k' c;

    assert(BP.points_to pf k2 k');
    assert(root_reachable il' k' /\ root_reachable il' k2);

    assert(is_proper_desc k2 k);
    lemma_proper_desc_depth_monotonic k2 k;

    lemma_not_init_equiv_root_reachable il' k;

    if pk <> k' then (
      if es = EACInit then (
        (* k is not root reachable since it is in EACInit *)
        assert(not (root_reachable il' k));

        (* this implies the proving ancestor is the ancestor with greatest depth that is root reachable *)
        assert(pk = first_root_reachable_ancestor pf k);
        lemma_proper_desc_depth_monotonic k pk;

        (* by construction pk is the ancestor with the greatest depth *)
        lemma_first_root_reachable_ancestor_greatest_depth pf k k';
        assert(depth k' <= depth pk);

        let aux(): Lemma (is_proper_desc pk k')
          = lemma_two_ancestors_related k k' pk;
            if is_desc k' pk then
              lemma_proper_desc_depth_monotonic k' pk
        in
        aux();
        lemma_two_related_desc_same_dir k pk k';
        lemma_reachable_between pf pk k';
        assert(is_desc pk k2);
        lemma_desc_depth_monotonic pk k2
      )
      else (
        assert(root_reachable il' k);
        lemma_reachable_between pf k k';
        assert(is_desc k k2);
        lemma_desc_depth_monotonic k k2
      )
    )

let lemma_addm_ancestor_is_proving (#app #n:_) (il: verifiable_log app n {length il > 0}):
  Lemma (requires (let n = length il in
                   let il' = I.prefix il (n-1) in
                   let e = I.index il (n-1) in
                   is_eac il' /\ AddM? e))
        (ensures (let n = length il in
                  let e = I.index il (n - 1) in
                  let il' = I.prefix il (n - 1) in
                  let AddM _ k k' = e in
                  Root <> k /\ k' = proving_ancestor il' k))
  = let i = length il - 1 in
    match addm_type il i with
    | NoNewEdge -> lemma_addm_ancestor_is_proving_nonewedge il
    | NewEdge -> lemma_addm_ancestor_is_proving_newedge il
    | CutEdge -> lemma_addm_ancestor_is_proving_cutedge il

let is_in_blum_snoc
  (#app #n:_)
  (bk: base_key)
  (il: eac_log app n {length il > 0})
  : Lemma (ensures (let i = length il - 1 in
                    let il' = prefix il i in
                    let es' = eac_state_of_key bk il' in
                    let es = eac_state_of_key bk il in
                    let e = index il i in
                    match e with
                    | AddM _ k _ -> if bk = k then not (is_in_blum es)
                                    else is_in_blum es = is_in_blum es'
                    | AddB _ _ _ _ -> is_in_blum es = is_in_blum es'
                    | EvictM k _ -> if bk = k then not (is_in_blum es)
                                    else is_in_blum es = is_in_blum es'
                    | EvictB k _ -> is_in_blum es = is_in_blum es'
                    | EvictBM k _ _ -> if bk = k then is_in_blum es
                                       else is_in_blum es = is_in_blum es'
                    | _ -> is_in_blum es = is_in_blum es'))
  = admit()

let lemma_proving_ancestor_blum_bit_addm_newedge_extend
  (#app #n:_)
  (il: eac_log app n{length il > 0})
  (ki: base_key {ki <> Root})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     AddM? (index il i) /\
                     addm_type il i = NewEdge /\
                     proving_ancestor_has_blum_bit il' ki))
          (ensures (proving_ancestor_has_blum_bit il ki))
  = let es = eac_state_of_key ki il in
    let pk = proving_ancestor il ki in
    let i = length il - 1 in

    let il' = prefix il i in
    let es' = eac_state_of_key ki il' in
    let pk' = proving_ancestor il' ki in
    let pf' = eac_ptrfn il' in

    let AddM (gk,gv) k k' = index il i in
    let c = desc_dir k k' in
    let v' = eac_merkle_value k' il' in
    let dh' = desc_hash v' c in

    eac_state_unchanged_snoc ki il;
    eac_state_transition_snoc ki il;
    lemma_proving_ancestor_snoc il ki;
    lemma_addm_ancestor_is_proving il;
    is_in_blum_snoc ki il;

    if es <> EACInit then (

      if ki = k then
        eac_value_snoc (IntK k') il
      else if ki = k' then
        eac_value_snoc (IntK pk') il
      else (
        (* the proving ancestor remains unchanged except for descendants of k, but ki is not one of them as
         * proved below *)
        assert(es = es');

        (* ki is root reachable since es' <> EACInit *)
        lemma_not_init_equiv_root_reachable il' ki;
        assert(root_reachable il' ki);

        (* k' is also root reachable since it is in store (so not EACInit)*)
        lemma_eac_instore_implies_root_reachable il' k';
        assert(root_reachable il' k');

        (* ki is not a descendant of k' along direction c since k' points to nothing along c *)
        let aux()
          : Lemma (ensures (not (is_desc ki (child c k'))))
          = if is_desc ki (child c k') then
               lemma_reachable_between pf' ki k'
        in
        aux();

        let aux ()
          : Lemma (ensures (not (is_proper_desc ki k)))
          = if is_desc ki k then
               lemma_desc_transitive ki k (child c k')
        in
        aux();

        (* since ki is not descendant of k, its proving ancestor remains unchanged *)
        assert(pk' = pk);
        eac_value_snoc (IntK pk') il
      )
    )

let lemma_proving_ancestor_blum_bit_addm_cutedge_extend
  (#app #n:_)
  (il: eac_log app n{length il > 0})
  (ki: base_key {ki <> Root})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     AddM? (index il i) /\
                     addm_type il i = CutEdge /\
                     proving_ancestor_has_blum_bit il' ki))
          (ensures (proving_ancestor_has_blum_bit il ki))
  = let es = eac_state_of_key ki il in
    let i = length il - 1 in
    let il' = prefix il i in
    let pk' = proving_ancestor il' ki in
    let AddM (gk,gv) k k' = index il i in
    let c = desc_dir k k' in

    eac_state_unchanged_snoc ki il;
    eac_state_transition_snoc ki il;
    lemma_proving_ancestor_snoc il ki;
    lemma_addm_ancestor_is_proving il;
    is_in_blum_snoc ki il;

    if es <> EACInit then (
      if ki = cutedge_desc il i then (
        eac_value_snoc (IntK k) il;
        lemma_eac_ptrfn il' k' c;
        lemma_points_to_implies_proving_ancestor il' ki k' c
      )
      else
        eac_value_snoc (IntK pk') il
    )

let lemma_proving_ancestor_blum_bit_addm_extend
  (#app #n:_)
  (il: eac_log app n{length il > 0})
  (ki: base_key {ki <> Root})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     AddM? (index il i) /\
                     proving_ancestor_has_blum_bit il' ki))
          (ensures (proving_ancestor_has_blum_bit il ki))
  = let es = eac_state_of_key ki il in
    let i = length il - 1 in
    let il' = prefix il i in
    let pk' = proving_ancestor il' ki in
    let AddM (gk,gv) k k' = index il i in
    let c = desc_dir k k' in
    let am = addm_type il i in

    eac_state_unchanged_snoc ki il;
    eac_state_transition_snoc ki il;
    lemma_proving_ancestor_snoc il ki;
    lemma_addm_ancestor_is_proving il;
    is_in_blum_snoc ki il;

    match am with
    | NoNewEdge ->
      if es <> EACInit then eac_value_snoc (IntK pk') il
    | NewEdge -> lemma_proving_ancestor_blum_bit_addm_newedge_extend il ki
    | CutEdge -> lemma_proving_ancestor_blum_bit_addm_cutedge_extend il ki

(* when evicted as blum the proving ancestor contains a bit indicating the eviction *)
let rec lemma_proving_ancestor_blum_bit (#app #n:_) (il: eac_log app n) (ki:base_key{ki <> Root}):
  Lemma (ensures (proving_ancestor_has_blum_bit il ki))
        (decreases (length il))
  = let es = eac_state_of_key ki il in
    if length il = 0 then
      eac_state_empty ki il
    else (
      let i = length il - 1 in
      let il' = prefix il i in
      let pk' = proving_ancestor il' ki in
      let e = index il i in

      eac_state_unchanged_snoc ki il;
      eac_state_transition_snoc ki il;
      lemma_proving_ancestor_snoc il ki;
      is_in_blum_snoc ki il;
      lemma_proving_ancestor_blum_bit il' ki;
      eac_value_snoc (IntK pk') il;

      match e with
      | AddM _ _ _ -> lemma_proving_ancestor_blum_bit_addm_extend il ki
      | EvictBM _ _ _ ->
        //lemma_evictm_ancestor_is_proving il i
        admit()
      | RunApp _ _ _ ->
        runapp_refs_only_leafkeys il i pk'
      | _ -> ()
    )

let store_contains_snoc
  (#app #n:_)
  (il: eac_log app n {length il > 0})
  (ki: base_key)
  (ti: nat{ti < n})
  : Lemma (ensures (let i = length il - 1 in
                    let il' = prefix il i in
                    let e = index il i in
                    let t = src il i in
                    let st = thread_store ti il in
                    let st' = thread_store ti il' in

                    match e with
                    | AddM _ k _
                    | AddB _ k _ _ -> if ki = k && t = ti then store_contains st ki
                                     else store_contains st ki = store_contains st' ki
                    | EvictB k _
                    | EvictBM k _ _
                    | EvictM k _ -> if ki = k && t = ti then not (store_contains st ki)
                                     else store_contains st ki = store_contains st' ki
                    | _ -> store_contains st ki = store_contains st' ki))
  = admit()

let store_contains_addm_ancestor
  (#app #n:_)
  (il: eac_log app n)
  (i: seq_index il {AddM? (index il i)})
  : Lemma (ensures (let AddM _ k k' = index il i in
                    let t = src il i in
                    let st_pre = thread_store_pre t il i in
                    let st_post = thread_store_post t il i in
                    store_contains st_pre k' /\ store_contains st_post k' /\ store_contains st_post k))
          [SMTPat (index il i)]
  = admit()

let has_instore_merkle_desc
  (#app #n:_)
  (il: eac_log app n)
  (k: base_key)
  (c: bin_tree_dir)
  (t: nat{t < n})
  : bool
  = let st = thread_store t il in
    is_merkle_key k &&
    (
      let mv = eac_merkle_value k il in
      points_to_some mv c &&
      (let kd = pointed_key mv c in
      store_contains st kd &&
      add_method_of st kd = MAdd))

let store_contains_evictm_ancestor
  (#app #n:_)
  (il: eac_log app n)
  (i: seq_index il {is_merkle_evict (index il i)})
  : Lemma (ensures (let k' = ancestor_slot (index il i) in
                    let k = evict_slot (index il i) in
                    let t = src il i in
                    let st_pre = thread_store_pre t il i in
                    let st_post = thread_store_post t il i in
                    let il' = prefix il i in
                    store_contains st_pre k /\ store_contains st_pre k' /\ store_contains st_post k' /\
                    not (has_instore_merkle_desc il' k Left t) /\
                    not (has_instore_merkle_desc il' k Right t)))
          [SMTPat (index il i)]
  = admit()

let store_contains_no_merkle_desc
  (#app #n:_)
  (il: eac_log app n)
  (i: seq_index il {is_evict (index il i)})
  : Lemma (ensures (let k = evict_slot (index il i) in
                    let t = src il i in
                    let il' = prefix il i in
                    not (has_instore_merkle_desc il' k Left t) /\
                    not (has_instore_merkle_desc il' k Right t)))
          [SMTPat (index il i)]
  = admit()

let proving_ancestor_of_merkle_instore
  (#app #n:_)
  (il: eac_log app n)
  (k: base_key)
  (t: nat{t < n})
  = let es = eac_state_of_key k il in
    let st = thread_store t il in
    k <> Root ==>
    EACInStore? es ==>
    EACInStore?.m es = MAdd ==>
    store_contains st k ==>
    store_contains st (proving_ancestor il k)

let lemma_store_contains_proving_ancestor_addm_newedge_extend
  (#app #n:_)
  (il: eac_log app n{length il > 0})
  (ki: base_key)
  (t:nat {t < n})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     AddM? (index il i) /\
                     addm_type il i = NewEdge /\
                     proving_ancestor_of_merkle_instore il' ki t))
          (ensures (proving_ancestor_of_merkle_instore il ki t))
  = let st = thread_store t il in
    let es = eac_state_of_key ki il in
    let i = length il - 1 in
    let t' = src il i in
    let il' = prefix il i in
    let st' = thread_store t il' in
    let es' = eac_state_of_key ki il' in
    let pf' = eac_ptrfn il' in

    let AddM _ k k' = index il i in
    let c = desc_dir k k' in

    eac_state_unchanged_snoc ki il;
    eac_state_transition_snoc ki il;
    store_contains_snoc il ki t;

    if ki <> Root && EACInStore? es && EACInStore?.m es = MAdd && store_contains st ki then (
      lemma_proving_ancestor_snoc il ki;
      let pk' = proving_ancestor il' ki in
      store_contains_snoc il pk' t;

      if ki = k then (
        key_in_unique_store k il t t';
        lemma_addm_ancestor_is_proving il
      )
      else if ki <> k' then (
        (* the proving ancestor remains unchanged except for descendants of k, but ki is not one of them as
         * proved below *)
        assert(es = es');

        (* ki is root reachable since es' <> EACInit *)
        lemma_not_init_equiv_root_reachable il' ki;
        assert(root_reachable il' ki);

        (* k' is also root reachable since it is in store (so not EACInit)*)
        let aux()
          : Lemma (root_reachable il' k')
          =  if k' = Root then lemma_reachable_reflexive pf' Root
            else lemma_eac_instore_implies_root_reachable il' k'
        in
        aux();

        (* ki is not a descendant of k' along direction c since k' points to nothing along c *)
        let aux()
          : Lemma (ensures (not (is_desc ki (child c k'))))
          = if is_desc ki (child c k') then
               lemma_reachable_between pf' ki k'
        in
        aux();

        let aux ()
          : Lemma (ensures (not (is_proper_desc ki k)))
          = if is_desc ki k then
               lemma_desc_transitive ki k (child c k')
        in
        aux();

        (* since ki is not descendant of k, its proving ancestor remains unchanged *)
        assert(pk' = proving_ancestor il ki);
        ()
      )
    )

let lemma_store_contains_proving_ancestor_addm_cutedge_extend
  (#app #n:_)
  (il: eac_log app n{length il > 0})
  (ki: base_key)
  (t:nat {t < n})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     AddM? (index il i) /\
                     addm_type il i = CutEdge /\
                     proving_ancestor_of_merkle_instore il' ki t))
          (ensures (proving_ancestor_of_merkle_instore il ki t))
  = let st = thread_store t il in
    let es = eac_state_of_key ki il in
    let i = length il - 1 in
    let t' = src il i in
    let il' = prefix il i in

    let AddM _ k k' = index il i in
    let c = desc_dir k k' in

    eac_state_unchanged_snoc ki il;
    eac_state_transition_snoc ki il;
    store_contains_snoc il ki t;

    if ki <> Root && EACInStore? es && EACInStore?.m es = MAdd && store_contains st ki then (
      lemma_proving_ancestor_snoc il ki;
      let pk' = proving_ancestor il' ki in
      store_contains_snoc il pk' t;

      if ki = k then (
        key_in_unique_store k il t t';
        lemma_addm_ancestor_is_proving il
      )
      else if ki = cutedge_desc il i then (
        lemma_eac_ptrfn il' k' c;
        lemma_points_to_implies_proving_ancestor il' ki k' c;
        //assert(proving_ancestor il ki = k);
        //assert(proving_ancestor il' ki = k');
        //assert(store_contains st' ki);
        key_in_unique_store k' il' t t';
        assert(t = t');
        ()
      )
    )

let lemma_store_contains_proving_ancestor_addm_nonewedge_extend
  (#app #n:_)
  (il: eac_log app n{length il > 0})
  (ki: base_key)
  (t:nat {t < n})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     AddM? (index il i) /\
                     addm_type il i = NoNewEdge /\
                     proving_ancestor_of_merkle_instore il' ki t))
          (ensures (proving_ancestor_of_merkle_instore il ki t))
  = let st = thread_store t il in
    let es = eac_state_of_key ki il in
    let i = length il - 1 in
    let t' = src il i in
    let il' = prefix il i in

    let AddM _ k k' = index il i in
    let c = desc_dir k k' in

    eac_state_unchanged_snoc ki il;
    eac_state_transition_snoc ki il;
    store_contains_snoc il ki t;

    if ki <> Root && EACInStore? es && EACInStore?.m es = MAdd && store_contains st ki then (
      lemma_proving_ancestor_snoc il ki;
      let pk' = proving_ancestor il' ki in
      store_contains_snoc il pk' t;
      if ki = k then (
        key_in_unique_store k il t t';
        lemma_addm_ancestor_is_proving il
      )
    )

let lemma_store_contains_proving_ancestor_addm_extend
  (#app #n:_)
  (il: eac_log app n{length il > 0})
  (ki: base_key)
  (t:nat {t < n})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     AddM? (index il i) /\
                     proving_ancestor_of_merkle_instore il' ki t))
          (ensures (proving_ancestor_of_merkle_instore il ki t))
  = match addm_type il (length il - 1)  with
    | NoNewEdge -> lemma_store_contains_proving_ancestor_addm_nonewedge_extend il ki t
    | NewEdge -> lemma_store_contains_proving_ancestor_addm_newedge_extend il ki t
    | CutEdge -> lemma_store_contains_proving_ancestor_addm_cutedge_extend il ki t

let lemma_store_contains_proving_ancestor_evictm_extend
  (#app #n:_)
  (il: eac_log app n{length il > 0})
  (ki: base_key)
  (t: nat{ t < n })
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     is_merkle_evict (index il i) /\
                     proving_ancestor_of_merkle_instore il' ki t))
          (ensures (proving_ancestor_of_merkle_instore il ki t))
  = let st = thread_store t il in
    let es = eac_state_of_key ki il in
    let i = length il - 1 in
    let t' = src il i in
    let il' = prefix il i in
    let k = evict_slot (index il i) in
    let k'  = ancestor_slot (index il i) in
    let c = desc_dir k k' in

    eac_state_unchanged_snoc ki il;
    eac_state_transition_snoc ki il;
    store_contains_snoc il ki t;
    if ki <> Root && EACInStore? es && EACInStore?.m es = MAdd && store_contains st ki then (
      lemma_proving_ancestor_snoc il ki;
      let pk' = proving_ancestor il' ki in
      let pf' = eac_ptrfn il' in
      store_contains_snoc il pk' t;

      if ki = k then
        lemma_evictm_ancestor_is_proving il i
      else if pk' = k then (
        (* k is being evicted but it is the proving ancestor of ki, which is in store of thread t *)
        let st' = thread_store t il' in

        (* we know that k is in store t' before evicting, so t = t' *)
        key_in_unique_store k il' t t';
        //assert(t = t');

        // since k is the proving ancestor of ki, it points to ki
        //assert(BP.points_to pf' ki k);

        // since eac add method of ki is MAdd (from es), it follows that
        // k has a merkle descendant in store, which is a contradiction since
        // this should have verification failure
        key_in_unique_store ki il' t (stored_tid ki il');
        assert(t = stored_tid ki il');
        eac_add_method_is_stored_addm il' ki;
        ()
      )
    )

let lemma_store_contains_proving_ancestor_evictb_extend
  (#app #n:_)
  (il: eac_log app n{length il > 0})
  (ki: base_key)
  (t: nat{ t < n })
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     EvictB? (index il i) /\
                     proving_ancestor_of_merkle_instore il' ki t))
          (ensures (proving_ancestor_of_merkle_instore il ki t))
  = let st = thread_store t il in
    let es = eac_state_of_key ki il in
    let i = length il - 1 in
    let t' = src il i in
    let il' = prefix il i in
    let k = evict_slot (index il i) in

    eac_state_unchanged_snoc ki il;
    eac_state_transition_snoc ki il;
    store_contains_snoc il ki t;
    if ki <> Root && EACInStore? es && EACInStore?.m es = MAdd && store_contains st ki then (
      lemma_proving_ancestor_snoc il ki;
      let pk' = proving_ancestor il' ki in
      let pf' = eac_ptrfn il' in
      store_contains_snoc il pk' t;

      if pk' = k then (
        (* k is being evicted but it is the proving ancestor of ki, which is in store of thread t *)
        let st' = thread_store t il' in

        (* we know that k is in store t' before evicting, so t = t' *)
        key_in_unique_store k il' t t';
        //assert(t = t');

        // since k is the proving ancestor of ki, it points to ki
        //assert(BP.points_to pf' ki k);

        // since eac add method of ki is MAdd (from es), it follows that
        // k has a merkle descendant in store, which is a contradiction since
        // this should have verification failure
        key_in_unique_store ki il' t (stored_tid ki il');
        assert(t = stored_tid ki il');
        eac_add_method_is_stored_addm il' ki;
        ()
      )
    )

let rec lemma_store_contains_proving_ancestor_aux
  (#app #n:_)
  (il: eac_log app n)
  (k: base_key)
  (t:nat {t < n})
  : Lemma (ensures (proving_ancestor_of_merkle_instore il k t))
          (decreases (length il))
  = let st = thread_store t il in
    let es = eac_state_of_key k il in
    if length il = 0 then
      eac_state_empty k il
    else (
      let i = length il - 1 in
      let il' = prefix il i in
      let st' = thread_store t il' in
      let e = index il i in

      eac_state_unchanged_snoc k il;
      eac_state_transition_snoc k il;
      store_contains_snoc il k t;
      lemma_store_contains_proving_ancestor_aux il' k t;

      if k <> Root && EACInStore? es && EACInStore?.m es = MAdd && store_contains st k then (
        lemma_proving_ancestor_snoc il k;
        let pk' = proving_ancestor il' k in
        store_contains_snoc il pk' t;

        match e with
        | AddM _ _ _ ->
          lemma_store_contains_proving_ancestor_addm_extend il k t
        | EvictBM _ _ _
        | EvictM _ _ ->
          lemma_store_contains_proving_ancestor_evictm_extend il k t
        | EvictB _ _ ->
          lemma_store_contains_proving_ancestor_evictb_extend il k t
        | RunApp _ _ _ ->
          runapp_refs_only_leafkeys il i pk'
        | _ -> ()
      )
    )

(* if the store contains a k, it contains its proving ancestor *)
let lemma_store_contains_proving_ancestor (#app #n:_) (il: eac_log app n) (tid:nat{tid < n}) (k:base_key{k <> Root}):
  Lemma (requires (let es = eac_state_of_key k il in
                   EACInStore? es /\
                   EACInStore?.m es = MAdd))
        (ensures (let pk = proving_ancestor il k in
                  let st = thread_store tid il in
                  store_contains st k ==> store_contains st pk))
  = lemma_store_contains_proving_ancestor_aux il k tid

