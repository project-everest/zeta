module Zeta.Generic.Global

let lemma_prefix_verifiable #vspec (gl: verifiable_log vspec) (i:nat{i <= S.length gl})
  : Lemma (ensures (verifiable (SA.prefix gl i)))
          [SMTPat (SA.prefix gl i)]
  = admit()

let add_sseq (#vspec:_) (gl: verifiable_log vspec)
  : ss:sseq (ms_hashfn_dom vspec.app) { S.length ss = S.length gl }
  = admit()

let evict_sseq (#vspec:_) (gl: verifiable_log vspec)
  : ss:sseq (ms_hashfn_dom vspec.app) { S.length ss = S.length gl }
  = admit()

let appfn_calls
  (#vspec: verifier_spec)
  (gl: verifiable_log vspec): sseq (Zeta.AppSimulate.appfn_call_res vspec.app)
  = admit()

let appfn_calls_within_ep
  (#vspec: verifier_spec)
  (ep: epoch)
  (gl: verifiable_log vspec): sseq (Zeta.AppSimulate.appfn_call_res vspec.app)
  = admit()
