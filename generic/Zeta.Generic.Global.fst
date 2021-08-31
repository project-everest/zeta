module Zeta.Generic.Global

let add_set
  (#vspec: verifier_spec)
  (ep: epoch)
  (gl: verifiable_log vspec): mset_ms_hashfn_dom vspec.app
  = admit()

let evict_set
  (#vspec: verifier_spec)
  (ep: epoch)
  (gl: verifiable_log vspec): mset_ms_hashfn_dom vspec.app
  = admit()
