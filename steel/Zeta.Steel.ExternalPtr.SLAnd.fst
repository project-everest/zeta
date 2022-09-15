module Zeta.Steel.ExternalPtr.SLAnd
friend Steel.Memory
friend Steel.Heap

module SEA = Steel.Effect.Atomic
module SC = Steel.ST.Coercions

let sl_and p1 p2 =
  to_vprop (hp_of p1 `Steel.Memory.h_and` hp_of p2)

let star_sl_and' (#opened: _) (p1 p2: vprop) : SEA.SteelGhostT unit opened
  (p1 `star` p2)
  (fun _ -> p1 `sl_and` p2)
= SEA.rewrite_slprop
    (p1 `star` p2)
    (p1 `sl_and` p2)
    (fun m -> () (* works thanks to `friend`ing *) )

let star_sl_and p1 p2 =
  SC.coerce_ghost (fun _ -> star_sl_and' p1 p2)
