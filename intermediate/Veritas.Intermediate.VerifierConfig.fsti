module Veritas.Intermediate.VerifierConfig

type verifier_config = 
  | VConfig: store_size: nat -> nthreads: nat -> verifier_config

let store_size (vc: verifier_config): nat = 
  VConfig?.store_size vc
