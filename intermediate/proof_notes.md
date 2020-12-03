# Proof Notes

## Notation

* `Spec.foo`: spec-level function `foo`.
* `Inter.foo`: intermediate-level function `foo`.
* The thread-local state for intermediate-level verification includes an `is_map` flag that is set to true if a duplicate key is ever added to the store.
* `logS_to_logK`: for a SINGLE verifier thread, given a slot-based log `logS` for which intermediate-level verification succeeds (output has Valid type, but `is_map` may be false), produces a corresponding key-based log `logK`.
* `glogS_to_logK`: given a verifiable global slot-based log, applies `logS_to_logK` to every verifier thread's log to produce a global key-based log.
* `ilogS_to_logK`: converts a verifiable interleaved global slot-based log to a interleaved global key-based log.
* Important note: `logS_to_logK`, etc. do not necesarily produce a *verifiable* key-based log. We will only prove that this is the case when all the `is_map` flags are true, and the resulting key-based log is EAC. We require the EAC constraint so that we can use invariants about `proving_ancestor` from Veritas.Verifier.Merkle.

## Proof Sketch

Assuming appropriate definitions for `to_state_op_gvlog`, `create`, etc. we can directly follow the proof of `lemma_verifier_correct` in Veritas.Verifier.Correctness (copied below). Note that `glogS_to_glogK` is defined for the input log `gl` because it is hash-verifiable and we can prove that `Inter.to_state_op_gvlog gl = Spec.to_state_op_gvlog (glogS_to_logK gl)`, meaning that the `g_ops` and `ts_ops` variables below have the same values in both the spec- and intermediate-level proofs.

```
let lemma_verifier_correct (gl: hash_verifiable_log { ~ (seq_consistent (to_state_op_gvlog gl))}):
  hash_collision_gen =    
  (* sequences of per-thread put/get operations *)
  let g_ops = to_state_op_gvlog gl in

  (* sequence ordered by time of each log entry *)
  let itsl = create gl in  
  lemma_interleaving_correct itsl;
  assert(interleave (i_seq itsl) gl);

  (* sequence of state ops induced by tmsl *)
  let ts_ops = state_ops itsl in

  lemma_vlog_interleave_implies_state_ops_interleave (i_seq itsl) gl;
  assert(interleave ts_ops g_ops);

  (* if ts_ops is read-write consistent then we have a contradiction *)
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
    lemma_time_seq_rw_consistent itsl // <-- this is the only interesting part
```
Above, the only hard part is proving an intermediate-level version of `lemma_time_seq_rw_consistent itsl`. This lemma says that given a hash-verifiable interleaved log `itsl` such that `state_ops itsl` is not read-write consistent, we can produce a hash collision. 

The structure of the proof might be something like the following:
* If `ilogS_to_logK itsl` is EAC, then we should be able to prove that after verifying `itsl` all `is_map` flags are true (may be tricky?). And from this, we should be able to prove that Inter.verify simulates Spec.verify, implying that `ilogS_to_logK itsl` is hash-verifiable. But now we have a contradiction because `Spec.lemma_eac_implies_state_ops_rw_consistent` says that `state_ops (ilogS_to_logK itsl) = state_ops itsl` is read-write consistent.
* Otherwise, `ilogS_to_logK itsl` is not EAC. In this case, we can't prove that the corresponding spec-level log is hash-verifiable, so we can't directly use `lemma_non_eac_time_seq_implies_hash_collision` from Veritas.Verifier.EAC. However, we can reuse the proofs of cases that do not require the input log to be hash-verifiable -- which is every case except the addb cases. I still need to think about what the addb cases will look like.

Thoughts on proving that `ilogS_to_logK itsl` is EAC ==> all `is_map` flags are true.
* The only way `is_map` can become false is during vaddb or vaddm, when the input key is already in the store. Is EAC has not been violated up to this point, then it is certainly violated at this add (?)
* TODO
