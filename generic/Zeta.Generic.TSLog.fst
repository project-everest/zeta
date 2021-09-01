module Zeta.Generic.TSLog

let lemma_prefix_clock_sorted (#vspec:_) (itsl: its_log vspec) (i:nat{i <= I.length itsl}):
  Lemma (ensures (clock_sorted (I.prefix itsl i)))
  = admit()


let create (#vspec:_) (gl: G.verifiable_log vspec): (itsl:its_log vspec{to_glog itsl == gl})
  = admit()
