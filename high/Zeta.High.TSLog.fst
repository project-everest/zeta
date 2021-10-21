module Zeta.High.TSLog

let neac_before_epoch_implies_neac #app #n (ep: epoch) (itsl: neac_before_epoch app n ep)
  : Lemma (ensures (not (is_eac itsl)))
          [SMTPat (prefix_within_epoch ep itsl)]
  = let il_ep = prefix_within_epoch ep itsl in
    assert(il_ep = prefix itsl (S.length il_ep));
    ()
