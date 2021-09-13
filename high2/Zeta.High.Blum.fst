module Zeta.High.Blum

open Zeta.High.Thread

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
                    | EACInit, EACInStore m gk v ->
                      AddM? e
                    | EACInStore _ gk' _, EACEvictedBlum gk v t tid ->
                      gk' = gk /\ is_blum_evict il i /\
                      to_base_key gk = evict_slot (index il i) /\
                      (let be = blum_evict_elem il i in
                       let gke,ve = be.r in
                       let open Zeta.MultiSetHashDomain in
                       gke = gk /\ ve = v /\ be.t = t /\ be.tid = tid)
                    | EACInStore _ _ _, EACEvictedMerkle _ _ ->
                      EvictM? e
                    | EACEvictedBlum gk v t tid, EACInStore _ gk' _ ->
                      gk = gk' /\ is_blum_add il i /\
                      to_base_key gk = add_slot (index il i) /\
                      (let be = blum_add_elem il i in
                       let open Zeta.MultiSetHashDomain in
                       let gke, ve = be.r in
                       gke = gk /\ ve = v /\ be.t = t /\ be.tid = tid
                      )
                    | EACEvictedMerkle _ _, EACInStore _ _ _ ->
                      AddM? e
                    | _ -> False)))
  = admit()

let eac_state_unchanged_snoc
  (#app #n:_)
  (ep: epoch)
  (gk: key app)
  (il: eac_log app n {length il > 0})
  : Lemma (ensures (let i = length il - 1 in
                    let il' = prefix il i in
                    let bk = to_base_key gk in
                    let es' = eac_state_of_key bk il' in
                    let es = eac_state_of_key bk il in
                    es' = es ==> (not (is_blum_add_of_key ep gk il i) /\
                                  not (is_blum_evict_of_key ep gk il i))))
  = admit()

let rec evict_add_count_rel
  (#app #n:_)
  (ep: epoch)
  (gk: key app)
  (il: eac_log app n)
  : Lemma (ensures(match eac_state_of_gkey gk il with
                   | EACFail -> False
                   | EACInit
                   | EACInStore _ _ _
                   | EACEvictedMerkle _ _ ->
                     size (k_add_set ep gk il) = size (k_evict_set ep gk il)
                   | EACEvictedBlum gke _ t _ ->
                     if t.e = ep && gke = gk then
                       size (k_add_set ep gk il) + 1 = size (k_evict_set ep gk il)
                     else
                       size (k_add_set ep gk il) = size (k_evict_set ep gk il)))
          (decreases (length il))
  = let bk = to_base_key gk in
    if length il = 0
    then (
      k_add_set_empty ep gk il;
      k_evict_set_empty ep gk il;
      eac_state_empty bk il
    )
    else (
      let i = length il - 1 in
      let il' = prefix il  i in
      k_add_set_snoc ep gk il;
      k_evict_set_snoc ep gk il;
      evict_add_count_rel ep gk il';
      eac_state_transition_snoc bk il;
      let es = eac_state_of_key bk il in
      let es' = eac_state_of_key bk il' in
      if es = es' then eac_state_unchanged_snoc ep gk il
      else ()
    )

let evict_elem_fixes_eac_state_key
  (#app #n:_)
  (il: eac_log app n)
  (i: seq_index il {is_blum_evict il i})
  : Lemma (ensures (let be = blum_evict_elem il i in
                    let gk,_ = be.r in
                    let bk = to_base_key gk in
                    let es = eac_state_of_key bk il in
                    is_eac_state_active bk il /\
                    to_gen_key bk il = gk))
  = admit()

let eac_instore_addb_diff_elem
  (#app #n:_)
  (itsl: its_log app n)
  (i: seq_index itsl{let itsli = prefix itsl i in
                     is_blum_add itsl i /\
                     is_eac itsli /\
                     (let e = index itsl i in
                      let k = add_slot e in
                      let es = eac_state_of_key k itsli in
                      EACInStore? es)})
  : (be':ms_hashfn_dom app{let ep = be'.t.e in
                           let as = add_set ep itsl in
                           let es = evict_set ep itsl in
                           let be = blum_add_elem itsl i in
                           mem be' as > mem be' es /\
                           be.t.e = ep})
  = let itsli = prefix itsl i in
    let itsli' = prefix itsl (i+1) in
    let e = index itsl i in
    let k = add_slot e in
    let be = blum_add_elem itsl i in
    let ep = be.t.e in
    let gk,_ = be.r in

    //assert(to_base_key gk = k);
    evict_add_count_rel ep gk itsli;
    //assert(size (k_add_set ep gk itsli) = size (k_evict_set ep gk itsli));
    k_add_set_snoc ep gk itsli';
    k_evict_set_snoc ep gk itsli';

    let be' = diff_elem (k_add_set ep gk itsli') (k_evict_set ep gk itsli') in
    k_add_set_correct ep gk itsli' be';
    add_set_rel_k_add_set ep gk itsli' be';
    evict_set_rel_k_evict_set ep gk itsli' be';
    //assert(mem be' (add_set ep itsli') > mem be' (evict_set ep itsli'));

    lemma_evict_before_add2 ep itsl (i+1) be';
    be'

let eac_evictedm_addb_diff_elem
  (#app #n:_)
  (itsl: its_log app n)
  (i:seq_index itsl{let itsli = prefix itsl i in
                    is_blum_add itsl i /\
                    is_eac itsli /\
                    (let e = index itsl i in
                     let k = add_slot e in
                     let es = eac_state_of_key k itsli in
                     EACEvictedMerkle? es)})
  : (be':ms_hashfn_dom app{let ep = be'.t.e in
                           let as = add_set ep itsl in
                           let es = evict_set ep itsl in
                           let be = blum_add_elem itsl i in
                           mem be' as > mem be' es /\
                           be.t.e = ep})
  = let itsli = prefix itsl i in
    let itsli' = prefix itsl (i+1) in
    let e = index itsl i in
    let k = add_slot e in
    let be = blum_add_elem itsl i in
    let ep = be.t.e in
    let gk,_ = be.r in

    //assert(to_base_key gk = k);
    evict_add_count_rel ep gk itsli;
    //assert(size (k_add_set ep gk itsli) = size (k_evict_set ep gk itsli));
    k_add_set_snoc ep gk itsli';
    k_evict_set_snoc ep gk itsli';

    let be' = diff_elem (k_add_set ep gk itsli') (k_evict_set ep gk itsli') in
    k_add_set_correct ep gk itsli' be';
    add_set_rel_k_add_set ep gk itsli' be';
    evict_set_rel_k_evict_set ep gk itsli' be';
    //assert(mem be' (add_set ep itsli') > mem be' (evict_set ep itsli'));

    lemma_evict_before_add2 ep itsl (i+1) be';
    be'

let eac_evictedb_addb_diff_elem
  (#app #n:_)
  (itsl: its_log app n)
  (i: seq_index itsl{let itsli = prefix itsl i in
                     let itsli' = prefix itsl (i + 1) in
                     is_blum_add itsl i /\
                     is_eac itsli /\
                     not (is_eac itsli') /\
                     (let e = index itsl i in
                      let k = add_slot e in
                      let es = eac_state_of_key k itsli in
                      EACEvictedBlum? es)})
  : (be':ms_hashfn_dom app{let ep = be'.t.e in
                           let as = add_set ep itsl in
                           let es = evict_set ep itsl in
                           let be = blum_add_elem itsl i in
                           mem be' as > mem be' es /\
                           be.t.e = ep})
  = let itsli = prefix itsl i in
    let itsli' = prefix itsl (i+1) in
    let e = index itsl i in
    let k = add_slot e in
    let be = blum_add_elem itsl i in
    let ep = be.t.e in
    let gk,_ = be.r in

    //assert(to_base_key gk = k);
    evict_add_count_rel ep gk itsli;
    admit()

(* when the eac store is evicted, there exists a previous evict *)
let previous_evict_of_eac_evicted
  (#app #n:_)
  (itsl: eac_log app n)
  (k: base_key {EACEvictedBlum? (eac_state_of_key k itsl)})
  : i:seq_index itsl{is_blum_evict itsl i /\
                     (let be = blum_evict_elem itsl i in
                      let EACEvictedBlum gk v t j = eac_state_of_key k itsl in
                      let gk',v' = be.r in
                      let open Zeta.MultiSetHashDomain in
                      gk = gk' /\ v = v' /\ be.t = t /\ be.tid = j)}
  = admit()
