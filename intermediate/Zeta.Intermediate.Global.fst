module Zeta.Intermediate.Global

open FStar.Classical

module GT = Zeta.Generic.Thread

let global_rel_implies_appfn_identical (#vcfg:_) (gls: verifiable_log vcfg) (glk: _{global_rel gls glk})
  : Lemma (ensures (app_fcrs gls = app_fcrs glk))
  = let fcrss = app_fcrs gls in
    let fcrsk = app_fcrs glk in

    assert(S.length fcrss = S.length fcrsk);
    let aux (t:_)
      : Lemma (ensures (S.index fcrss t == S.index fcrsk t))
      = let tls = index gls t in
        let tlk = index glk t in
        eliminate forall t. IT.thread_rel (index gls t) (index glk t)
        with t;
        assert(IT.thread_rel tls tlk);
        IT.thread_rel_implies_fcrs_identical tls tlk
    in
    forall_intro aux;
    assert(S.equal fcrss fcrsk)
