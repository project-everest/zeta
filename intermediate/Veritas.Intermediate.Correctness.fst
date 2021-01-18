module Veritas.Intermediate.Correctness

open Veritas.Hash
open Veritas.Record
open Veritas.SeqMachine
open Veritas.State
open Veritas.StateSeqMachine
open Veritas.Verifier.EAC
open Veritas.Intermediate.Global
open Veritas.Intermediate.Thread
open Veritas.Intermediate.VerifierConfig

module I = Veritas.Interleave
module IntG = Veritas.Intermediate.Global
module IntTL = Veritas.Intermediate.TSLog


let lemma_time_seq_rw_consistent  #vcfg
  (il: IntTL.hash_verifiable_log vcfg {~ (rw_consistent (IntTL.to_state_ops il))})
  : hash_collision_gen = admit()

// final correctness property
let lemma_verifier_correct (#vcfg:_) (gl: hash_verifiable_log vcfg { ~ (seq_consistent (IntG.to_state_ops gl))})
  : hash_collision_gen = 
  (* sequences of per-thread put/get operations *)
  let g_ops = IntG.to_state_ops gl in
  
  (* sequence ordered by time of each log entry *)
  let il = IntTL.create gl in  
  I.lemma_interleaving_correct il;
  assert(I.interleave (I.i_seq il) gl);

  (* sequence of state ops induced by tmsl *)
  let ts_ops = IntTL.to_state_ops il in
  IntTL.lemma_logS_interleave_implies_state_ops_interleave (I.i_seq il) gl;
  assert(I.interleave ts_ops g_ops);

  let is_rw_consistent = valid_all_comp ssm ts_ops in
  lemma_state_sm_equiv_rw_consistent ts_ops;

    if is_rw_consistent then (
      assert(valid_all ssm ts_ops);
      assert(rw_consistent ts_ops);

      (* a contradiction *)
      assert(seq_consistent g_ops);

      (* any return value *)
      SingleHashCollision (Collision (DVal Null) (DVal Null))
    )
    else
      lemma_time_seq_rw_consistent il
