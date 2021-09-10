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


let lemma_neac_implies_hash_collision
  (#app #n:_)
  (epmax: epoch)
  (itsl: neac_before_epoch app n epmax {GB.aems_equal_upto epmax itsl})
  : hash_collision app
  = let fi = eac_failure itsl in
    eac_boundary_not_appfn itsl;

    match fi.es with
    | EACInit -> (
      match fi.le with
      | AddB _ _ _ _ -> lemma_non_eac_init_addb epmax itsl
      | AddM _ _ _ -> lemma_non_eac_init_addm itsl
      | EvictM _ _ -> lemma_non_eac_init_evict itsl
      | EvictB _ _ -> lemma_non_eac_init_evict itsl
      | EvictBM _ _ _ -> lemma_non_eac_init_evict itsl
      | _ -> hash_collision_contra app
    )
    | EACInStore _ _ _ -> (
      match fi.le with
      | AddB _ _ _ _ -> lemma_non_eac_instore_addb epmax itsl
      | _ -> admit()
    )
    | _ ->

    admit()
