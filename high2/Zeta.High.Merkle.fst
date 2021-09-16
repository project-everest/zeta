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
                      | NewEdge -> if k' = bkf
                                   then
                                     let v' = eac_merkle_value k' il' in
                                     let v' = update_value v' c k Zeta.Hash.zero false in
                                     eac_value gkf il = IntV v'
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
  : option(kd:bin_tree_node{is_desc kd (child c k)})
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

let lemma_eac_ptrfn
  (#app #n:_)
  (il: eac_log app n)
  (k: merkle_key)
  (c:bin_tree_dir)
  : Lemma (ensures (let pf = eac_ptrfn il in
                    let v = eac_merkle_value k il in
                    points_to_none v c /\ pf k c = None \/
                    points_to_some v c /\ is_desc (pointed_key v c) (child c k) /\
                    pf k c = Some (pointed_key v c)))
          [SMTPat (eac_ptrfn il k c)]
  = let pf = eac_ptrfn il in
    let v = eac_merkle_value k il in
    if points_to_none v c then ()
    else (
      let kd = pointed_key v c in
      eac_ptrfn_empty_or_points_to_desc il k c;
      ()
    )

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
                      match (addm_type il i) with
                      | NoNewEdge -> feq_ptrfn pf pf'
                      | NewEdge -> True//feq_ptrfn pf (extend_ptrfn pf' k k')
                      | _ -> True
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

      lemma_eac_ptrfn il Root c;
      assert(None = pf Root c);
      lemma_non_reachable_desc_of_none pf k Root
    )
    else
      let i = length il - 1 in
      let il' = prefix il i in
      let e = index il i in
      let es' = eac_state_of_key k il' in
      eac_state_unchanged_snoc k il;
      eac_state_transition_snoc k il;
      if es = es' then admit()
      else

      admit()


(* the ancestor who holds the proof of the value of key k *)
let proving_ancestor (#app #n:_) (il: eac_log app n) (k:base_key{k <> Root}):
  k':base_key{is_proper_desc k k'}
  = admit()

(* after the first add the proving ancestor always points to self *)
let lemma_proving_ancestor_points_to_self (#app #n:_) (il: eac_log app n) (k:base_key{k <> Root}):
  Lemma (requires (eac_state_of_key k il <> EACInit))
        (ensures (let pk = proving_ancestor il k in
                  let d = desc_dir k pk in
                  let v = eac_merkle_value pk il in
                  points_to v d k))
  = admit()

(* before the first add the proving ancestor points to none or to a key that is not an ancestor *)
let lemma_proving_ancestor_initial (#app #n:_) (il: eac_log app n) (k:base_key{k <> Root}):
  Lemma (requires (eac_state_of_key k il = EACInit))
        (ensures (let k' = proving_ancestor il k in
                  let v' = eac_merkle_value k' il in
                  let c = desc_dir k k' in
                  points_to_none v' c \/
                  not (is_desc k (pointed_key v' c))))
  = admit()

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
  = admit()

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
