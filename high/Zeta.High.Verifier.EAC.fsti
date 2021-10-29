module Zeta.High.Verifier.EAC

open Zeta.Time
open Zeta.HashCollision
open Zeta.EAC
open Zeta.Generic.Interleave
open Zeta.High.Verifier
open Zeta.High.TSLog

module GI = Zeta.Generic.Interleave
module GB = Zeta.Generic.Blum

val lemma_neac_implies_hash_collision
  (#app #n:_)
  (epmax: epoch)
  (itsl: neac_before_epoch app n epmax {GB.aems_equal_upto epmax itsl})
  : hash_collision app

let provides_hash_collision
  (#app #n:_)
  (itsl: Zeta.High.Interleave.neac_log app n)
  = let open Zeta.High.Interleave in
    let i = eac_boundary itsl in
    match Zeta.Interleave.index itsl i with
    | Zeta.GenericVerifier.AddB _ _ _ _ -> false
    | _ -> true

val lemma_neac_implies_hash_collision_simple
  (#app #n:_)
  (itsl: Zeta.High.Interleave.neac_log app n {provides_hash_collision itsl})
  : hash_collision app
