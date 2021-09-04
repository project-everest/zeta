module Zeta.Generic.TSLog

(* clock is idxfn_t, so has the prefix property *)
let lemma_prefix_clock_sorted (#vspec #n:_) (itsl: its_log vspec n) (i:nat{i <= length itsl}):
  Lemma (ensures (clock_sorted (prefix itsl i)))
  = admit()

let create (#vspec:_) (gl: G.verifiable_log vspec): (itsl:its_log vspec (S.length gl){to_glog itsl == gl})
  = admit()
