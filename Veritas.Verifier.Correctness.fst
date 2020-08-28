module Veritas.Verifier.Correctness

open FStar.Seq
open Veritas.EAC
open Veritas.Hash
open Veritas.Interleave
open Veritas.Key
open Veritas.MultiSetHash
open Veritas.Record
open Veritas.SeqAux
open Veritas.SeqMachine
open Veritas.StateSeqMachine
open Veritas.State
open Veritas.Verifier
open Veritas.Verifier.EAC
open Veritas.Verifier.Global
open Veritas.Verifier.Thread
open Veritas.Verifier.TSLog

module S = FStar.Seq
module E = Veritas.EAC
module V = Veritas.Verifier
module VT = Veritas.Verifier.Thread
module VG = Veritas.Verifier.Global
module TL = Veritas.Verifier.TSLog

//Allow the solver to unroll recursive functions at most once (fuel)
//Allow the solver to invert inductive definitions at most once (ifuel)
#push-options "--max_fuel 1 --max_ifuel 1 --initial_fuel 1 --initial_ifuel 1"

(* 
 * an indexed version of time sequence where we track the source verifier thread 
 * for every log entry 
 *)
let time_seq_idx (gl: VG.hash_verifiable_log): TL.hash_verifiable_log (S.length gl) =
  admit()
  //interleaved_idx_seq gl (time_seq_ctor gl)

(* state ops of all vlogs of all verifier threads *)
let to_state_op_gvlog (gl: g_vlog) =
  map to_state_op_vlog gl

let lemma_time_seq_rw_consistent (#n:pos) 
  (itsl: TL.hash_verifiable_log n{~ (rw_consistent (to_state_op_vlog (project_seq itsl)))})
  : hash_collision_gen = 
  let tsl = project_seq itsl in  
  let tsle = time_seq_ext itsl in
  assert(to_vlog tsle = tsl);

  (* provided: the sequence of state ops is not rw-consistent *)
  let ts_ops = to_state_op_vlog tsl in
  assert(~ (rw_consistent ts_ops));

  (* if time seq log is evict add consistent, the underlying state ops is rw-consistent *)
  (* a contradiction *)
  if E.is_eac_log tsle then (
    lemma_eac_implies_rw_consistent tsle;
    assert(rw_consistent ts_ops);

    (* any return value *)
    SingleHashCollision (Collision (DVal Null) (DVal Null)) 
  )
  else 
    lemma_non_eac_time_seq_implies_hash_collision itsl

let lemma_vlog_interleave_implies_state_ops_interleave (l: vlog) (gl: g_vlog{interleave l gl}):
  Lemma (interleave (to_state_op_vlog l) (to_state_op_gvlog gl)) = admit()

(* final verifier correctness theorem *)
let lemma_verifier_correct (gl: VG.hash_verifiable_log { ~ (seq_consistent (to_state_op_gvlog gl))}):
  hash_collision_gen =    
  (* sequences of per-thread put/get operations *)
  let g_ops = to_state_op_gvlog gl in

  (* sequence ordered by time of each log entry *)
  let itsl = time_seq_idx gl in
  lemma_partition_idx_seq_interleaving itsl;
  let tsl = project_seq itsl in
  //assert(interleave tsl gl);
  assume(interleave tsl gl);

  (* sequence of state ops induced by tmsl *)
  let tm_ops = to_state_op_vlog tsl in

  lemma_vlog_interleave_implies_state_ops_interleave tsl gl;
  assert(interleave tm_ops g_ops);

  (* if tm_ops is read-write consistent then we have a contradiction *)
  let is_rw_consistent = valid_all_comp ssm tm_ops in

  if is_rw_consistent then (

    assert(valid_all ssm tm_ops);
    lemma_state_sm_equiv_rw_consistent tm_ops;
    assert(rw_consistent tm_ops);

    (* a contradiction *)
    assert(seq_consistent g_ops);

    (* any return value *)
    SingleHashCollision (Collision (DVal Null) (DVal Null))
  )
  else
    lemma_time_seq_rw_consistent itsl
  
