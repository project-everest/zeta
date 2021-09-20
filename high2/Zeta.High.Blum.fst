module Zeta.High.Blum

open Zeta.High.Verifier
open Zeta.High.Thread
open Zeta.SeqIdx

module V = Zeta.GenericVerifier
module G = Zeta.Generic.Global
module T = Zeta.Generic.Thread
module I = Zeta.Interleave
module MSD = Zeta.MultiSetHashDomain

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
                    | EACInStore _ _ _, EACInStore _ _ _ ->
                      RunApp? e
                    | _ -> False)))
  = let i = length il - 1 in
    let il' = prefix il i in
    let es' = eac_state_of_key bk il' in
    let es = eac_state_of_key bk il in
    let ee = mk_vlog_entry_ext il i in
    let e = index il i in
    let tid = src il i in
    let st_pre = thread_store_pre tid il i in
    eac_state_snoc bk il;
    if es = es' then ()
    else
    (
      assert(es <> EACFail);
      assert(es = eac_add ee es');
      match es' with
      | EACInStore _ gk' _ -> (
        match ee with
        | EvictBlum e v_e tid_e ->
          ext_evict_val_is_stored_val il i;
          key_in_unique_store bk il' tid (stored_tid bk il')
        | _ ->  ()
      )
      | EACEvictedBlum _ _ _ _ ->
        // TODO: never seen this; fails with assert commented
        assert(match es', es with EACEvictedBlum gk v t tid, EACInStore _ gk' _ -> True);
        ()
      | _ -> ()
    )

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
  = let bk = to_base_key gk in
    eac_state_snoc bk il

#push-options "--z3rlimit_factor 3"

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

#pop-options

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

#push-options "--z3rlimit_factor 3"

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

#pop-options

open Zeta.High.Verifier

let is_blum_evict_refs_key (#app:_) (k: base_key) (e: vlog_entry app)
  = let open Zeta.GenericVerifier in
    e `refs_key` k &&
    is_blum_evict e

(* switch order of params ... *)
let refs_key (#app:_) (k: base_key) (e: vlog_entry app)
  = e `refs_key` k

module SA = Zeta.SeqAux

#push-options "--z3rlimit_factor 3"

let rec last_evict_props
  (#app #n:_)
  (k: base_key)
  (itsl: eac_log app n {EACEvictedBlum? (eac_state_of_key k itsl)})
  : Lemma (ensures (let l = i_seq itsl in
                    let EACEvictedBlum gke ve te tide = eac_state_of_key k itsl in
                    exists_elems_with_prop (is_blum_evict_refs_key k) l /\
                    (let j = last_idx (is_blum_evict_refs_key k) l in
                     let MHDom (gk,v) t tid  = blum_evict_elem itsl j in
                     gk = gke /\ v = ve /\ t = te /\ tid = tide /\
                     j = last_idx (refs_key k) l)))
          (decreases length itsl)
  = let n = length itsl in
    if n = 0 then
      eac_state_empty k itsl
    else
      let i = n - 1 in
      let l = i_seq itsl in
      let itsl' = prefix itsl i in
      let l' = i_seq itsl' in
      let es = eac_state_of_key k itsl in
      //let EACEvictedBlum gke ve te tide = es in
      let es' = eac_state_of_key k itsl' in
      let e = index itsl i in
      eac_state_transition_snoc k itsl;
      eac_state_snoc k itsl;
      if es = es' then (
        last_evict_props k itsl';
        last_idx_snoc (refs_key k) l;
        last_idx_snoc (is_blum_evict_refs_key k) l
      )
      else (
        last_idx_correct (is_blum_evict_refs_key k) l i;
        last_idx_correct (refs_key k) l i
      )

#pop-options

module S = FStar.Seq

let to_blum_elem (#app:_) (#k: base_key) (es: eac_state app k{EACEvictedBlum? es})
  = let EACEvictedBlum gk v t j = es in
    let open Zeta.MultiSetHashDomain in
    MHDom (gk,v) t j

#push-options "--z3rlimit_factor 3"

let rec last_entry_blum_evict_implies_eac_state
  (#app #n:_)
  (k: base_key)
  (il: eac_log app n)
  : Lemma (requires (let l = i_seq il in
                     exists_elems_with_prop (refs_key k) l /\
                     is_blum_evict il (last_idx (refs_key k) l)))
          (ensures (let es = eac_state_of_key k il in
                    let i = last_idx (refs_key k) (i_seq il) in
                    let be = blum_evict_elem il i in
                    EACEvictedBlum? es /\
                    to_blum_elem es = be))
          (decreases (length il))
  = let p = refs_key #app k in
    let l = i_seq il in
    let i = last_idx p l in
    let n = length il in
    let es = eac_state_of_key k il in
    let il' = prefix il (n-1) in
    let l' = i_seq il' in
    let es' = eac_state_of_key k il' in
    let e = index il (n-1) in
    last_idx_snoc p l;
    eac_state_snoc k il;

    if refs_key k e then (
      assert(i = n - 1);
      eac_state_transition_snoc k il;
      ()
    )
    else
      last_entry_blum_evict_implies_eac_state k il'

#pop-options

let eac_transition_out_of_blum_evict
  (#app #n:_)
  (k: base_key)
  (il: eac_log app n)
  (i: seq_index il)
  : Lemma (requires (let es = eac_state_of_key_pre k il i in
                     EACEvictedBlum? es /\
                     refs_key k (index il i)))
          (ensures (let es' = eac_state_of_key_pre k il i in
                    let es = eac_state_of_key_post k il i in
                    is_blum_add il i /\ blum_add_elem il i = to_blum_elem es' /\
                    EACInStore? es))
  = let ili = prefix il (i+1) in
    eac_state_snoc k ili;
    eac_state_transition_snoc k ili

#push-options "--z3rlimit_factor 3"

let next_add
  (#app #n:_)
  (k: base_key)
  (itsl: eac_log app n)
  (i: seq_index itsl {let l = i_seq itsl in
                      is_blum_evict_refs_key k (index itsl i) /\
                      i < last_idx (refs_key k) l})
  : Tot(j:seq_index itsl{let l = i_seq itsl in
                     is_blum_add itsl j /\
                     blum_add_elem itsl j = blum_evict_elem itsl i /\
                     j > i /\ j <= last_idx (refs_key k) l})
    (decreases length itsl)
  = let p = refs_key #app k in
    let l = i_seq itsl in
    let j = next_idx p l i in
    let itsl_j = prefix itsl j in
    let l_j = i_seq itsl_j in
    exists_elems_with_prop_intro p l_j i;
    last_idx_correct p l_j i;
    assert(last_idx p l_j = i);
    last_entry_blum_evict_implies_eac_state k itsl_j;
    eac_transition_out_of_blum_evict k itsl j;
    j

#pop-options

module GV = Zeta.GenericVerifier

#push-options "--z3rlimit_factor 3"

let eac_evictedb_addb_diff_elem
  (#app #n:_)
  (il: neac_log app n {let i = eac_boundary il in
                         let k = eac_fail_key il in
                         Zeta.Generic.TSLog.clock_sorted il /\
                         is_blum_add il i /\
                         EACEvictedBlum? (eac_state_of_key_pre k il i)})
  : (be':ms_hashfn_dom app{let i = eac_boundary il in
                           let ep = be'.t.e in
                           let as = add_set ep il in
                           let es = evict_set ep il in
                           let be = blum_add_elem il i in
                           mem be' as > mem be' es /\
                           be.t.e = ep})
  = let i = eac_boundary il in
    let itsli = prefix il i in
    let k = eac_fail_key il in
    let EACEvictedBlum gk_e v_e t_e tid_e = eac_state_of_key_pre k il i in
    eac_state_transition k il i;
    lemma_cur_thread_state_extend il i;

    let be = blum_add_elem il i in
    let gk,v = be.r in
    let ep = be.t.e in

    // otherwise we would not have an EAC failure at i
    assert(gk <> gk_e || v <> v_e || be.t <> t_e || be.tid <> tid_e);

    if evict_set ep il `contains` be then (
      last_evict_props k itsli;

      let j = last_idx (is_blum_evict_refs_key #app k) (i_seq itsli) in
      let be' = blum_evict_elem il j in
      assert(be' <> be);

      let j' = evict_elem_idx il be in
      let e = index il j' in
      let be2 = blum_evict_elem il j' in
      assert(GV.is_blum_evict e);
      lemma_evict_before_add il i;
      assert(j' < i);
      lemma_index_prefix_property il i j';
      assert(index itsli j' = index il j');

      //assert(p (S.index s j'));
      last_idx_correct (is_blum_evict_refs_key #app k) (i_seq itsli) j';
      assert(j' < j);

      let i' = next_add k itsli j' in
      //assert(be = blum_add_elem il i');

      lemma_add_set_mem il i i';
      // assert(mem be (add_set ep il) >= 2);

      evict_set_is_a_set ep il;
      be
    )
    else
      be

#pop-options
