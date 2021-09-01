module Zeta.Generic.Global


let to_fm (#vspec: verifier_spec) (#b:eqtype) (#pred:_) (p:nat) (tfn: cond_idxfn_t #vspec b pred)
  : ssfm_t (verifier_log_entry vspec) b p
  = admit()
