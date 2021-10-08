module Zeta.Intermediate.VerifierConfig

open Zeta.App

noeq
type verifier_config =
  | VConfig: store_size: pos ->
             app: app_params ->
             verifier_config

let store_size (vc: verifier_config): nat =
  VConfig?.store_size vc

(* an index in store *)
let slot_id (vcfg:verifier_config) = i:nat{i < store_size vcfg}

let valid_slot (vcfg:verifier_config) (s:nat): bool =
  s < store_size vcfg
