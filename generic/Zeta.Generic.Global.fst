module Zeta.Generic.Global

let lemma_prefix_verifiable #vspec (gl: verifiable_log vspec) (i:nat{i <= S.length gl})
  : Lemma (ensures (verifiable (SA.prefix gl i)))
          [SMTPat (SA.prefix gl i)]
  = admit()

