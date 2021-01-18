module Veritas.Intermediate.Correctness

open Veritas.State
open Veritas.Verifier.EAC
open Veritas.Intermediate.Global
open Veritas.Intermediate.Thread
open Veritas.Intermediate.VerifierConfig

module IntG = Veritas.Intermediate.Global

// final correctness property
let lemma_verifier_correct (#vcfg:_) (gl: hash_verifiable_log vcfg { ~ (seq_consistent (IntG.to_state_ops gl))})
  : hash_collision_gen = 
  (* sequences of per-thread put/get operations *)
  let g_ops = IntG.to_state_ops gl in
  admit()
