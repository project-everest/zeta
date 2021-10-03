module Zeta.Generic.Global

open FStar.Classical

let lemma_prefix_verifiable #vspec (gl: verifiable_log vspec) (i:nat{i <= S.length gl})
  : Lemma (ensures (verifiable (SA.prefix gl i)))
  = let gl' = SA.prefix gl i in
    let aux (t:_)
      : Lemma (ensures (T.verifiable (t,S.index gl' t)))
      = eliminate
        forall (tid: SA.seq_index gl). T.verifiable (thread_log_base gl tid)
        with t
    in
    forall_intro aux
