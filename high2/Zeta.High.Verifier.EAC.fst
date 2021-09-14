module Zeta.High.Verifier.EAC

open Zeta.BinTree
open Zeta.Interleave
open Zeta.App
open Zeta.Key
open Zeta.GenKey
open Zeta.Merkle
open Zeta.Record
open Zeta.Time
open Zeta.MultiSet
open Zeta.MultiSetHashDomain
open Zeta.GenericVerifier
open Zeta.Generic.Blum
open Zeta.EAC
open Zeta.High.Verifier
open Zeta.High.Thread
open Zeta.High.Interleave
open Zeta.High.Merkle
open Zeta.High.Blum

module S = FStar.Seq
module I = Zeta.Interleave
module T = Zeta.Generic.Thread
module G = Zeta.Generic.Global
module GI=Zeta.Generic.Interleave
module GB = Zeta.Generic.Blum
module GTL=Zeta.Generic.TSLog
module HI=Zeta.High.Interleave
module HM = Zeta.High.Merkle
module HTL=Zeta.High.TSLog
module HV = Zeta.High.Verifier
module EAC = Zeta.EAC

noeq
type failure_info (app:app_params) (n:nat) = {
  bi: nat;
  bk: base_key;
  es: eac_state app bk;
  le: vlog_entry app;
  lee: ee:vlog_entry_ext app { to_vlog_entry ee = le /\ eac_add ee es = EACFail };
  vs_pre: v:vtls_t app {v.valid};
  vs_post: v:vtls_t app {v.valid /\ v == verify_step le vs_pre};
}

let eac_failure (#app #n:_) (il: neac_log app n)
  : failure_info app n
  = let bi = eac_boundary il in
    let bk = eac_fail_key il in
    let es = eac_state_of_key_pre bk il bi in
    let le = index il bi in
    let lee = mk_vlog_entry_ext il bi in
    let vs_pre = cur_thread_state_pre il bi in
    let vs_post = cur_thread_state_post il bi in
    lemma_cur_thread_state_extend il bi;
    eac_state_transition bk il bi;
    { bi; bk; es; le; lee; vs_pre; vs_post }

let lemma_non_eac_appfn_non_refs
  (#app #n:_)
  (itsl: neac_log app n
    {let fi = eac_failure itsl in
     not (fi.le `refs_key` fi.bk) /\
     RunApp? fi.le})
  : hash_collision app
  = let fi = eac_failure itsl in
    let i = fi.bi in
    ext_app_records_is_stored_val itsl i;
    hash_collision_contra app

let lemma_non_eac_init_appfn
  (#app #n:_)
  (itsl: neac_log app n
    {let fi = eac_failure itsl in
     (fi.es = EACInit || EAC.is_eac_state_evicted fi.es)  /\
     RunApp? fi.le})
  : hash_collision app
  = let fi = eac_failure itsl in
    let i = fi.bi in
    let itsli = prefix itsl i in
    let itsli' = prefix itsl (i+1) in
    let tid = src itsl i in
    let RunApp f p ss = fi. le in

    if fi.le `refs_key` fi.bk then (
      // parameter index of key fi.bk
      let pi = S.index_mem fi.bk ss in

      // k is the verifier store prior to processing ...
      let vs_pre = thread_state_pre tid itsl i in
      get_record_set_correct ss vs_pre pi;
      let st_pre = thread_store tid itsli in
      assert(store_contains st_pre fi.bk);
      FStar.Classical.exists_intro (fun tid -> store_contains (thread_store tid itsli) fi.bk) tid;
      lemma_instore fi.bk itsli;
      hash_collision_contra app
    )
    else lemma_non_eac_appfn_non_refs itsl

let lemma_non_eac_instore_appfn
  (#app #n:_)
  (itsl: neac_log app n
    {let fi = eac_failure itsl in
     EACInStore? fi.es /\
     fi.le `refs_key` fi.bk /\
     RunApp? fi.le})
  : hash_collision app
  = let fi = eac_failure itsl in
    let i = fi.bi in
    let itsli = prefix itsl i in
    let itsli' = prefix itsl (i+1) in
    let tid = src itsl i in
    let App (RunApp f p ss) rs = fi.lee in
    let EACInStore _ gk ev = fi.es in

    if not (fi.le `refs_key` fi.bk) then
      lemma_non_eac_appfn_non_refs itsl
    else (
      // parameter index of key fi.bk
      let pi = S.index_mem fi.bk ss in
      let vs_pre = cur_thread_state_pre itsl i in
      let st_pre = thread_store_pre tid itsl i in
      get_record_set_correct ss vs_pre pi;
      ext_app_records_is_stored_val itsl i;

      let ak,av = S.index rs pi in
      assert(AppK ak = stored_key st_pre fi.bk);
      assert(AppV av = HV.stored_value st_pre fi.bk);
      stored_key_is_correct fi.bk itsli;
      key_in_unique_store fi.bk itsli tid (stored_tid fi.bk itsli);
      assert(AppK ak = gk);

      eac_app_state_value_is_stored_value itsli gk;
      assert(AppV av = ev);

      hash_collision_contra app
    )

let lemma_non_eac_init_addb
  (#app #n:_)
  (epmax: epoch)
  (itsl: neac_before_epoch app n epmax
    {let fi = eac_failure itsl in
     GB.aems_equal_upto epmax itsl /\
     fi.es = EACInit /\
     AddB? fi.le})
  : hash_collision app
  = let fi = eac_failure itsl in
    let i = fi.bi in
    let be = blum_add_elem itsl i in
    let ep = be.t.e in
    let itsli = prefix itsl i in

    // since fi.es is EACInit, there cannot be a prior entry for fi.bk
    //assert(eac_state_of_key fi.bk itsli = EACInit);
    eac_state_init_implies_no_key_refs fi.bk itsli;
    //assert(~ (has_some_ref_to_key fi.bk itsli));

    if evict_set ep itsl `contains` be then (
      (* if evict set contains be, then the index of be should be prior to i *)
      let j = evict_elem_idx itsl be in
      lemma_evict_before_add itsl i;
      assert(j < i);

      (* this implies a prior reference to fi.bk which is a contradiction *)
      FStar.Classical.exists_intro (fun i -> refs_key (I.index itsli i) fi.bk) j;
      hash_collision_contra app
    )
    else (
      not_eq (add_set ep itsl) (evict_set ep itsl) be;
      hash_collision_contra app
    )

let lemma_non_eac_init_addm
  (#app #n:_)
  (itsl: neac_log app n
    {let fi = eac_failure itsl in
     fi.es = EACInit /\
     AddM? fi.le})
  : hash_collision app
  = let fi = eac_failure itsl in
    let i = fi.bi in
    let AddM (gk,v) k k' = index itsl i in
    let itsli = prefix itsl i in
    let itsli' = prefix itsl (i+1) in
    let tid = src itsl i in

    assert(eac_add fi.lee fi.es = EACFail);
    assert(v <> init_value gk);

    lemma_addm_ancestor_is_proving itsli';
    assert(k' = proving_ancestor itsli k);

    (* k' is in the verifier thread tid's cache before processing entry i *)
    let st_pre = thread_store_pre tid itsl i in
    assert(store_contains st_pre k');

    let gk' = IntK #app k' in
    eac_value_is_stored_value itsli gk' tid;
    let mv' = HM.eac_value k' itsli in
    let d = desc_dir k k' in
    let dh' = desc_hash mv' d in

    lemma_proving_ancestor_initial itsli k;

    match dh' with
    | Empty -> hash_collision_contra app
    | Desc k2 _ _ ->
      lemma_desc_reflexive k;
      hash_collision_contra app

let lemma_non_eac_init_evict
  (#app #n:_)
  (itsl: neac_log app n
    {let fi = eac_failure itsl in
     fi.es = EACInit /\
     is_evict fi.le})
  : hash_collision app
  = let fi = eac_failure itsl in
    let i = fi.bi in
    let k  = evict_slot fi.le in
    let itsli = prefix itsl i in
    let itsli' = prefix itsl (i+1) in
    let tid = src itsl i in

    // k is the verifier store prior to processing ...
    let st_pre = thread_store tid itsli in
    assert(store_contains st_pre k);

    let aux ()
      : Lemma (ensures (k <> Root))
      = root_never_evicted itsl i
    in
    aux();

    FStar.Classical.exists_intro (fun tid -> store_contains (thread_store tid itsli) k) tid;
    lemma_instore k itsli;
    hash_collision_contra app

let lemma_non_eac_instore_addb
  (#app #n:_)
  (epmax: epoch)
  (itsl: neac_before_epoch app n epmax
    {let fi = eac_failure itsl in
     GB.aems_equal_upto epmax itsl /\
     EACInStore? fi.es /\ AddB? fi.le})
  : hash_collision app
  = let fi = eac_failure itsl in
    let i = fi.bi in

    let be' = eac_instore_addb_diff_elem itsl i in
    let ep = be'.t.e in
    not_eq (add_set ep itsl) (evict_set ep itsl) be';
    hash_collision_contra app


let lemma_non_eac_instore_addm
  (#app #n:_)
  (itsl: neac_log app n
    {let fi = eac_failure itsl in
     EACInStore? fi.es /\
     AddM? fi.le})
  : hash_collision app
  = let fi = eac_failure itsl in
    let i = fi.bi in
    let itsli = prefix itsl i in
    let itsli' = prefix itsl (i+1) in
    let tid = src itsl i in
    let AddM (gk,_) k k' = fi.le in
    let addm = EACInStore?.m fi.es in

    let tid_stored = stored_tid fi.bk itsli in

    (* if store already contains k, adding should cause verification failure *)
    if tid = tid_stored then
      hash_collision_contra app
    else (

      (* k' is the proving ancestor of k *)
      lemma_addm_ancestor_is_proving itsli';

      if addm = BAdd then (

        (* this implies that the "blum bit" is set to false in k' *)
        lemma_proving_ancestor_blum_bit itsli k;

        (* this leads to a verification failure *)
        eac_value_is_stored_value itsli (IntK k') tid;

        hash_collision_contra app
      )
      else (
        (* k' is in the store of tid_stored, since k is in tid_stored *)
        lemma_store_contains_proving_ancestor itsli tid_stored k;

        (* which gives a contradiction since k' has to be in a unique store *)
        key_in_unique_store k' itsli tid tid_stored;

        hash_collision_contra app
      )
    )

let lemma_non_eac_instore_evict
  (#app #n:_)
  (itsl: neac_log app n
    {let fi = eac_failure itsl in
     EACInStore? fi.es /\
     is_evict fi.le})
  : hash_collision app
  = let fi = eac_failure itsl in
    let i = fi.bi in
    let itsli = prefix itsl i in
    let tid = src itsl i in
    let k  =  evict_slot fi.le in
    let EACInStore _ gk _ = fi.es in
    //let EvictMerkle _ v' = fi.lee in

    //let st_pre = thread_store tid itsli in
    //assert(store_contains st_pre k);
    //let gks = stored_key st_pre k in
    //let vk = HV.stored_value st_pre k in
    ext_evict_val_is_stored_val itsl i;
    //assert(v' = vk);

    //assert(AppV? v && v' <> v);
    eac_add_method_is_stored_addm itsli k;
    key_in_unique_store k itsli tid (stored_tid k itsli);
    eac_app_state_value_is_stored_value itsli gk;

    hash_collision_contra app

let lemma_non_eac_evicted_merkle_addm
  (#app #n:_)
  (itsl: neac_log app n
    {let fi = eac_failure itsl in
     EACEvictedMerkle? fi.es /\
     AddM? fi.le})
  : hash_collision app
  = let fi = eac_failure itsl in
    let i = fi.bi in
    let itsli = prefix itsl i in
    let itsli' = prefix itsl (i+1) in
    let tid = src itsl i in
    let AddM (gk,v) k k' = fi.le in
    let EACEvictedMerkle gk_e v_e = fi.es in

    (* k' is the proving ancestor of k *)
    lemma_addm_ancestor_is_proving itsli';
    // assert(k' = proving_ancestor itsli k);

    (* the stored value of k' points to k *)
    lemma_proving_ancestor_points_to_self itsli k;
    eac_value_is_stored_value itsli (IntK k') tid;

    (* invariant - the proving ancestors stores the hash of evicted value v_e *)
    lemma_proving_ancestor_has_hash itsli gk;
    eac_value_is_evicted_value itsli gk;

    assert(gk <> gk_e || v <> v_e);
    assert(to_base_key gk = to_base_key gk_e);
    if gk <> gk_e then
      let AppK k1 = gk in
      let AppK k2 = gk_e in
      KeyCollision k1 k2
    else
      ValueCollision v v_e

let lemma_non_eac_evicted_merkle_addb
  (#app #n:_)
  (epmax: epoch)
  (itsl: neac_before_epoch app n epmax
    {let fi = eac_failure itsl in
     GB.aems_equal_upto epmax itsl /\
     EACEvictedMerkle? fi.es /\
     is_blum_add fi.le})
  : hash_collision app
  = let fi = eac_failure itsl in
    let i = fi.bi in
    let be' = eac_evictedm_addb_diff_elem itsl i in
    let ep = be'.t.e in
    not_eq (add_set ep itsl) (evict_set ep itsl) be';
    hash_collision_contra app

let lemma_non_eac_evicted_evict
  (#app #n:_)
  (itsl: neac_log app n
    {let fi = eac_failure itsl in
     EAC.is_eac_state_evicted fi.es /\
     is_evict fi.le})
  : hash_collision app
  = let fi = eac_failure itsl in
    let i = fi.bi in
    let itsli = prefix itsl i in
    let tid = src itsl i in
    (* the following lemma says fi.bk does not exist in any store *)
    lemma_instore fi.bk itsli;
    assert(~ (exists_in_some_store fi.bk itsli));

    (* for verification to succeed fi.bk needs to be in store tid, a contradictio *)
    FStar.Classical.exists_intro (fun tid -> store_contains (thread_store tid itsli) fi.bk) tid;
    hash_collision_contra app

let lemma_non_eac_evicted_blum_addm
  (#app #n:_)
  (itsl: neac_log app n
    {let fi = eac_failure itsl in
     EACEvictedBlum? fi.es /\
     AddM? fi.le})
  : hash_collision app
  = let fi = eac_failure itsl in
    let i = fi.bi in
    let itsli = prefix itsl i in
    let itsli' = prefix itsl (i+1) in
    let tid = src itsl i in
    let AddM (gk,_) k k' = fi.le in

    (* k' is the proving ancestor of k *)
    lemma_addm_ancestor_is_proving itsli';
    assert(k' = proving_ancestor itsli k);

    lemma_proving_ancestor_points_to_self itsli k;
    eac_value_is_stored_value itsli (IntK k') tid;
    lemma_proving_ancestor_blum_bit itsli k;
    hash_collision_contra app

let lemma_non_eac_evicted_blum_addb
  (#app #n:_)
  (epmax: epoch)
  (itsl: neac_before_epoch app n epmax
    {let fi = eac_failure itsl in
     GB.aems_equal_upto epmax itsl /\
     EACEvictedBlum? fi.es /\
     AddB? fi.le})
  : hash_collision app
  = let fi = eac_failure itsl in
    let i = fi.bi in
    let be = eac_evictedb_addb_diff_elem itsl in
    let ep = be.t.e in
    //assert(be.t.e <= epmax);
    not_eq (add_set ep itsl) (evict_set ep itsl) be;
    hash_collision_contra app

let lemma_neac_implies_hash_collision
  (#app #n:_)
  (epmax: epoch)
  (itsl: neac_before_epoch app n epmax {GB.aems_equal_upto epmax itsl})
  : hash_collision app
  = let fi = eac_failure itsl in

    match fi.es with
    | EACInit -> (
      match fi.le with
      | RunApp _ _ _ -> lemma_non_eac_init_appfn itsl
      | AddB _ _ _ _ -> lemma_non_eac_init_addb epmax itsl
      | AddM _ _ _ -> lemma_non_eac_init_addm itsl
      | EvictM _ _ -> lemma_non_eac_init_evict itsl
      | EvictB _ _ -> lemma_non_eac_init_evict itsl
      | EvictBM _ _ _ -> lemma_non_eac_init_evict itsl
      | _ -> hash_collision_contra app
    )
    | EACInStore _ _ _ -> (
      match fi.le with
      | RunApp _ _ _ -> lemma_non_eac_instore_appfn itsl
      | AddB _ _ _ _ -> lemma_non_eac_instore_addb epmax itsl
      | AddM _ _ _ -> lemma_non_eac_instore_addm itsl
      | EvictM _ _ -> lemma_non_eac_instore_evict itsl
      | EvictB _ _ -> lemma_non_eac_instore_evict itsl
      | EvictBM _ _ _ -> lemma_non_eac_instore_evict itsl
      | _ -> hash_collision_contra app
    )
    | EACEvictedMerkle _ _ -> (
      match fi.le with
      | RunApp _ _ _ -> lemma_non_eac_init_appfn itsl
      | AddM _ _ _ -> lemma_non_eac_evicted_merkle_addm itsl
      | AddB _ _ _ _ -> lemma_non_eac_evicted_merkle_addb epmax itsl
      | EvictM _ _ -> lemma_non_eac_evicted_evict itsl
      | EvictB _ _ -> lemma_non_eac_evicted_evict itsl
      | EvictBM _ _ _ -> lemma_non_eac_evicted_evict itsl
      | _ -> hash_collision_contra app
    )
    | EACEvictedBlum _ _ _ _ -> (
      match fi.le with
      | RunApp _ _ _ -> lemma_non_eac_init_appfn itsl
      | AddM _ _ _ -> lemma_non_eac_evicted_blum_addm itsl
      | AddB _ _ _ _ -> lemma_non_eac_evicted_blum_addb epmax itsl
      | EvictM _ _ -> lemma_non_eac_evicted_evict itsl
      | EvictB _ _ -> lemma_non_eac_evicted_evict itsl
      | EvictBM _ _ _ -> lemma_non_eac_evicted_evict itsl
      | _ -> hash_collision_contra app
    )
