module Zeta.Intermediate.TSLog

open FStar.Classical

let lemma_vtls_rel_implies_spec_clock_sorted (#vcfg:_) (ils:its_log vcfg)
  : Lemma (requires (forall_vtls_rel ils))
          (ensures (let ilk = to_logk ils  in
                    T.clock_sorted ilk))
  = let ilk = to_logk ils in
    let open Zeta.Time in
    let aux (i j:_)
      : Lemma (ensures (i <= j ==> clock ilk i `ts_leq` clock ilk j))
      = lemma_vtls_rel_implies_same_clock ils i;
        lemma_vtls_rel_implies_same_clock ils j;
        assert(i <= j ==> clock ils i `ts_leq` clock ils j);
        ()
    in
    forall_intro_2 aux
