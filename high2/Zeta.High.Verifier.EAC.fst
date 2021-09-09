module Zeta.High.Verifier.EAC

open Zeta.App
open Zeta.Key
open Zeta.GenericVerifier
open Zeta.EAC
open Zeta.High.Interleave

module I = Zeta.Interleave
module GI=Zeta.Generic.Interleave
module GTL=Zeta.Generic.TSLog
module HI=Zeta.High.Interleave
module HTL=Zeta.High.TSLog
module IF=Zeta.IdxFn

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
    let es = IF.to_pre_fn (eac_state_of_key bk) il bi in
    let le = I.index il bi in
    { bi; bk; es; le}

let lemma_non_eac_init_addb
  (#app #n:_)
  (epmax: epoch)
  (itsl: neac_before_epoch app n epmax
    {let fi = eac_failure itsl in
     GI.aems_equal_upto epmax itsl /\
     fi.es = EACInit /\
     AddB? fi.le})
  = let fi = eac_failure itsl in
    let e = I.prefix itsl fi.bi in
    //let be = blum_add_elem itsl fi.bi in

    admit()

let lemma_neac_implies_hash_collision
  (#app #n:_)
  (epmax: epoch)
  (itsl: neac_before_epoch app n epmax {GI.aems_equal_upto epmax itsl})
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
