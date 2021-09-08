module Zeta.High.Verifier.EAC

open Zeta.Time
open Zeta.HashCollision
open Zeta.EAC
open Zeta.Generic.Interleave
open Zeta.High.Verifier
open Zeta.High.TSLog

module GI = Zeta.Generic.Interleave

val lemma_neac_implies_hash_collision
  (#app #n:_)
  (epmax: epoch)
  (itsl: neac_before_epoch app n epmax {GI.aems_equal_upto epmax itsl})
  : hash_collision app
