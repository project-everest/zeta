module Zeta.High.Verifier.EAC

open Zeta.Interleave
open Zeta.App
open Zeta.Key
open Zeta.GenKey
open Zeta.Time
open Zeta.MultiSet
open Zeta.MultiSetHashDomain
open Zeta.GenericVerifier
open Zeta.Generic.Blum
open Zeta.EAC
open Zeta.High.Thread
open Zeta.High.Interleave

module S = FStar.Seq
module I = Zeta.Interleave
module T = Zeta.Generic.Thread
module G = Zeta.Generic.Global
module GI=Zeta.Generic.Interleave
module GB = Zeta.Generic.Blum
module GTL=Zeta.Generic.TSLog
module HI=Zeta.High.Interleave
module HTL=Zeta.High.TSLog

type failure_info (app:app_params) (n:nat) = {
  bi: nat;
  bk: base_key;
  es: eac_state app bk;
  le: vlog_entry app
}

let eac_failure (#app #n:_) (il: neac_log app n)
  : failure_info app n
  = let bi = eac_boundary il in
    let bk = eac_fail_key il in
    let es = eac_state_of_key_pre bk il bi in
    let le = I.index il bi in
    { bi; bk; es; le}

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
      | _ ->
      admit()
    )
    | _ ->

    admit()
