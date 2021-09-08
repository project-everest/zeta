module Zeta.High.Verifier.EAC

open Zeta.High.Interleave

module GI=Zeta.Generic.Interleave
module GTL=Zeta.Generic.TSLog
module HI=Zeta.High.Interleave
module HTL=Zeta.High.TSLog

let lemma_neac_implies_hash_collision
  (#app #n:_)
  (epmax: epoch)
  (itsl: neac_before_epoch app n epmax {GI.aems_equal_upto epmax itsl})
  : hash_collision app
  = let i = HI.eac_boundary itsl in
    eac_boundary_not_appfn itsl;
    admit()
