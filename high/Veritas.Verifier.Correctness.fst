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

(* state ops of all vlogs of all verifier threads upto epoch ep *)
let to_state_op_gvlog (gl: g_vlog) =
  map to_state_op_vlog gl

let lemma_vlog_interleave_implies_state_ops_interleave (l: vlog) (gl: g_vlog{interleave #vlog_entry l gl})
  : Lemma (interleave #state_op (to_state_op_vlog l) (to_state_op_gvlog gl)) 
  = FStar.Squash.bind_squash
      #(interleave l gl)
      #(interleave (to_state_op_vlog l) (to_state_op_gvlog gl))
      ()
      (fun i -> 
        let i' = Veritas.Interleave.filter_map_interleaving is_state_op to_state_op i in
        FStar.Squash.return_squash i')

let lemma_time_seq_rw_consistent
  (epmax: epoch)
  (itsl: TL.hash_verifiable_log epmax {
    let itsl_ep = prefix_upto_epoch epmax itsl in
    ~ (rw_consistent (state_ops itsl_ep))})
  : hash_collision_gen =

  let itsl_ep = prefix_upto_epoch epmax itsl in
  let ts_ops = state_ops itsl_ep in
  assert(~ (rw_consistent ts_ops));

  if TL.is_eac itsl_ep then (
    // ts log is eac implies state ops in that sequence are rw-consistent
    TL.lemma_eac_implies_state_ops_rw_consistent itsl_ep;
    // ... which is a contradiction
    assert(rw_consistent ts_ops);
    (* any return value *)
    SingleHashCollision (Collision (DVal Null) (DVal Null))
  )
  else
    lemma_non_eac_time_seq_implies_hash_collision epmax itsl

(* final verifier correctness theorem *)
let lemma_verifier_correct
  (epmax: epoch)
  (gl: VG.hash_verifiable_log epmax { ~ (seq_consistent (to_state_op_gvlog (VG.prefix_upto_epoch epmax gl)))}):
  hash_collision_gen =

  (* log entries upto epoch epmax *)
  let gl_ep = VG.prefix_upto_epoch epmax gl in

  (* state ops in the first epmax epochs *)
  let g_ops = to_state_op_gvlog gl_ep in

  (* sequence ordered by time of each log entry *)
  let itsl = TL.create gl in

  (* log entries upto epoch epmax *)
  let itsl_ep = prefix_upto_epoch epmax itsl in
  assert(gl_ep = g_vlog_of itsl_ep);
  lemma_interleaving_correct itsl_ep;
  assert(interleave (i_seq itsl_ep) gl_ep);

  (* sequence of state ops projected from time ordered sequence *)
  let ts_ops = state_ops itsl_ep in
  lemma_vlog_interleave_implies_state_ops_interleave (i_seq itsl_ep) gl_ep;
  assert(interleave ts_ops g_ops);

  (* if tm_ops is read-write consistent then we have a contradiction *)
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
    lemma_time_seq_rw_consistent epmax itsl
