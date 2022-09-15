module Zeta.Steel.ExternalPtr.SLAnd

open Steel.ST.Util

// Non-separating conjunct
val sl_and (p1 p2: vprop) : vprop

val star_sl_and (#opened: _) (p1 p2: vprop) : STGhostT unit opened
  (p1 `star` p2)
  (fun _ -> p1 `sl_and` p2)
