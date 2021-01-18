module Veritas.Intermediate.Correctness

(*
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
module IntTS = Veritas.Intermediate.TSLog
module SpecTS = Veritas.Verifier.TSLog

(* property that:
 *    (a) the intermediate verifiers all satisfy the store invariant
 *    (b) the intermediate and spec level verifiers states correspond to one-another (related)
 *    (c) the spec level log is time sorted (b and c imply that the spec log has type its_log)
 *    (d) the spec level log is evict-add-consistent 
 *)
let store_inv_rel_spec_eac #vcfg (il: IntTS.its_log vcfg) = 
  let il_k = ilogS_to_logK il in
  forall_store_ismap il /\
  forall_vtls_rel il il_k /\
  SpecTS.clock_sorted il_k /\
  SpecTS.is_eac il_k



val lemma_il_hash_verifiable_implies_eac_and_vtls_rel #vcfg (il: il_hash_verifiable_log vcfg)
  : store_inv_rel_spec_eac_or_hashcollision il     


let lemma_time_seq_rw_consistent  #vcfg
  (il: IntTL.hash_verifiable_log vcfg {~ (rw_consistent (IntTL.to_state_ops il))})
  : hash_collision_gen = 
  let tsl = I.i_seq il in  
  let ts_ops = IntTL.to_state_ops tsl in
  let hc_or_inv = lemma_il_hash_verifiable_implies_eac_and_vtls_rel il in
  (* if hc_or_inv returns a hash collision, then we can return the same collision *)
  if Some? hc_or_inv
  then Some?.v hc_or_inv

  (* otherwise, we can use the spec-level lemma *)
  else (
    assert (store_inv_rel_spec_eac il);
    
    let il_k = ilogS_to_logK il in

    lemma_forall_vtls_rel_implies_spec_hash_verifiable il il_k;
    assert (SpecTS.hash_verifiable il_k);

    lemma_ilogS_to_logK_state_ops il;
    assert (state_ops il == SpecTS.state_ops il_k);

    SpecC.lemma_time_seq_rw_consistent il_k  
  )

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
*)
