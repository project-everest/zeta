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

let addm_props (#app #n:_) (il: eac_log app n) (i: seq_index il{AddM? (index il i)})
  : Lemma (ensures (let AddM (gk, gv) k k' = index il i in
                    let il' = prefix il i in
                    EACInStore? (eac_state_of_key_pre k' il i) /\
                    EACInStore? (eac_state_of_key_post k' il i) /\
                    is_proper_desc k k' /\
                    (let v' = eac_merkle_value k' il' in
                     let c = desc_dir k k' in
                     let dh' = desc_hash v' c in
                     match dh' with
                     | Empty -> gv = init_value gk
                     | Desc k2 h2 b2 -> (k2 = k /\ h2 = hashfn gv /\ b2 = false) \/
                                        (is_proper_desc k2 k /\ gv = init_value gk))))
          [SMTPat (index il i)]
  = admit()

let addm_type (#app #n:_) (il: eac_log app n) (i: seq_index il{AddM? (index il i)})
  : addm_t
  = let AddM (gk, gv) k k' = index il i in
    let il' = prefix il i in
    let v' = eac_merkle_value k' il' in
    let c = desc_dir k k' in
    let dh' = desc_hash v' c in
    match dh' with
    | Empty -> NewEdge
    | Desc k2 h2 b2 -> if k2 = k then NoNewEdge else CutEdge

let cutedge_desc (#app #n:_) (il: eac_log app n) (i:_{addm_type il i = CutEdge})
  = let AddM (gk, gv) k k' = index il i in
    let il' = prefix il i in
    let v' = eac_merkle_value k' il' in
    let c = desc_dir k k' in
    let dh' = desc_hash v' c in
    match dh' with
    | Desc k2 h2 b2 -> k2

let evictm_props (#app #n:_) (il: eac_log app n) (i: seq_index il{EvictM? (index il i)})
  : Lemma (ensures (let EvictM k k' = index il i in
                    let il' = prefix il i in
                    let esk = eac_state_of_key_pre k il i in
                    let esk' = eac_state_of_key_pre k' il i in
                    is_proper_desc k k' /\ EACInStore? esk /\ EACInStore? esk'))
          [SMTPat (index il i)]
  = admit()

let evictbm_props (#app #n:_) (il: eac_log app n) (i: seq_index il{EvictBM? (index il i)})
  : Lemma (ensures (let EvictBM k k' _ = index il i in
                    let il' = prefix il i in
                    let esk = eac_state_of_key_pre k il i in
                    let esk' = eac_state_of_key_pre k' il i in
                    is_proper_desc k k' /\ EACInStore? esk /\ EACInStore? esk'))
          [SMTPat (index il i)]
  = admit()

let only_data_keys_ref_runapp (#app #n:_) (il: eac_log app n) (i: seq_index il{RunApp? (index il i)}) (k: base_key)
  : Lemma (ensures (let e = index il i in
                    e `refs_key` k ==> is_leaf_key k))
  = admit()

let eac_value_init
  (#app #n:_)
  (gk: key app)
  (il: eac_log app n {length il = 0})
  : Lemma (ensures (eac_value gk il = init_value gk))
  = admit()

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
                                       let gk = to_gen_key k il' in
                                       let v = eac_value gk il' in
                                       let c = desc_dir k k' in
                                       let v' = update_value v' c k (hashfn v) false in
                                       eac_value gkf il = IntV v'
                                     else
                                       eac_value gkf il = eac_value gkf il'
                    | EvictB _ _ -> eac_value gkf il = eac_value gkf il'
                    | EvictBM k k' _ -> if k' = bkf then
                                       let v' = eac_merkle_value k' il' in
                                       let gk = to_gen_key k il' in
                                       let v = eac_value gk il' in
                                       let c = desc_dir k k' in
                                       let v' = update_value v' c k (hashfn v) false in
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
  = admit()

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
                    match es', es with
                    | EACInit, EACInStore _ _ _ -> AddM? e
                    | EACInStore _ _ _ , EACEvictedBlum _ _ _ _ -> V.is_blum_evict e
                    | EACInStore _ _ _ , EACEvictedMerkle _ _ -> EvictM? e
                    | EACEvictedBlum _ _ _ _, EACInStore _ _ _ -> AddB? e
                    | EACEvictedMerkle _ _, EACInStore _ _ _ -> AddM? e
                    | EACInStore _ _ _, EACInStore _ _ _ -> RunApp? e
                    | _ -> False)))
  = admit()

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
                    RunApp? e))
  = admit()

let eac_ptrfn_aux (#app #n:_) (il: eac_log app n) (k:merkle_key) (c:bin_tree_dir)
  : option (base_key)
  = let v = eac_merkle_value k il in
    if M.points_to_none v c
    then None
    else Some (M.pointed_key v c)

let rec eac_ptrfn_empty_or_points_to_desc
  (#app #n:_)
  (il: eac_log app n)
  (k: merkle_key)
  (c: bin_tree_dir)
  : Lemma (ensures (eac_ptrfn_aux il k c = None \/
                    (let k' = Some?.v (eac_ptrfn_aux il k c) in
                     is_desc k' (child c k))))
          (decreases (length il))
  = if length il = 0 then
      eac_value_init (IntK k) il
    else
      let i = length il - 1  in
      let il' = prefix il i in
      let e = index il i in
      eac_ptrfn_empty_or_points_to_desc il' k c;
      eac_value_snoc (IntK k) il;
      match e with
      | RunApp _ _ _ -> only_data_keys_ref_runapp il i k
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
                                   BP.points_to_some pf' k c /\
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
  = admit()

let proving_ancestor_has_hash (#app #n:_) (il: eac_log app n) (gk:key app{gk <> IntK Root})
  = let k = to_base_key gk in
    let es = eac_state_of_key k il in
    let pk = proving_ancestor il k in
    let mv = eac_merkle_value pk il in
    let c = desc_dir k pk in
    let v = eac_value gk il in
    EACEvictedMerkle? es ==> pointed_hash mv c = hashfn v

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

      lemma_eac_instore_implies_root_reachable il' k';
      assert(root_reachable il' k');

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
      match e with
      | AddM _ _ _ -> lemma_proving_ancestor_has_hash_addm_extend il gk
      | EvictM _ _ -> admit()
      | EvictBM _ _ _ -> admit()
      | AddB _ _ _ _
      | EvictB _ _
      | NextEpoch
      | VerifyEpoch ->
        eac_value_snoc (IntK pk') il
      | RunApp _ _ _ ->
        admit()
    )

(* when evicted as merkle the proving ancestor contains our hash *)
let lemma_proving_ancestor_has_hash (#app #n:_) (il: eac_log app n) (gk:key app{gk <> IntK Root}):
  Lemma (requires (let k = to_base_key gk in
                   EACEvictedMerkle? (eac_state_of_key k il)))
        (ensures (let k = to_base_key gk in
                  let pk = proving_ancestor il k in
                  let mv = eac_merkle_value pk il in
                  let c = desc_dir k pk in
                  let v = HI.eac_value gk il in
                  pointed_hash mv c = hashfn v))
  = lemma_proving_ancestor_has_hash_aux il gk

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
  = admit()


(* when evicted as blum the proving ancestor contains a bit indicating the eviction *)
let lemma_proving_ancestor_blum_bit (#app #n:_) (il: eac_log app n) (k:base_key{k <> Root}):
  Lemma (ensures (proving_ancestor_has_blum_bit il k))
  = admit()

(* if the store contains a k, it contains its proving ancestor *)
let lemma_store_contains_proving_ancestor (#app #n:_) (il: eac_log app n) (tid:nat{tid < n}) (k:base_key{k <> Root}):
  Lemma (requires (let es = eac_state_of_key k il in
                   EACInStore? es /\
                   EACInStore?.m es = MAdd))
        (ensures (let pk = proving_ancestor il k in
                  let st = thread_store tid il in
                  store_contains st k ==> store_contains st pk))
  = admit()


(* precond: k' is a proper ancestor of k, but not the proving ancestor.
 *          k' is also initialized (previously added)
 * ensures: k' points to something along direction (k' -> k) and that something is an ancestor of pk
 *)
let lemma_init_ancestor_ancestor_of_proving
  (#app #n:_)
  (il: eac_log app n)
  (k:base_key)
  (k':base_key{is_proper_desc k k'}):
  Lemma (requires ((k' = Root \/ eac_state_of_key k' il <> EACInit) /\
                    k' <> proving_ancestor il k))
        (ensures (let d = desc_dir k k' in
                  let mv = eac_merkle_value k' il in
                  let pk = proving_ancestor il k in
                  points_to_some mv d /\
                  is_desc pk (pointed_key mv d)))
  = admit()

(* if a merkle value of key k points to a key kd in some direction d, then kd is a proper desc of
 * k in direction d *)
let lemma_points_to_dir_correct (#app #n:_) (il: eac_log app n) (k:merkle_key) (d:bin_tree_dir):
  Lemma (requires (let mv = eac_merkle_value k il in
                   points_to_some mv d))
        (ensures (let mv = eac_merkle_value k il in
                  let kd = pointed_key mv d in
                  is_proper_desc kd k /\
                  d = desc_dir kd k))
  = admit()
