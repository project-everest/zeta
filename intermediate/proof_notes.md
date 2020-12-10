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

We will prove this by induction on the global, interleaved log. Assuming a hash collision has not occurred, we will need to maintain several invariants.
* The spec-level log corresponding to the interleaved intermediate log is evict-add consistent.
* Every verifier thread has its `is_map` flag set to true.
* Every verifier's store satisifes the following property.
  ```
  let exists_unique (#t:eqtype) (f: t → prop) = ∃ (x:t). f x ∧ (∀ (y:t{x ≠ y}). ¬ (f y))
  let merkle_inv (st:vstore)
    = ∀ (k:key{k ≠ Root}).
      store_contains_key_with_MAdd st k ⟺
      (exists (s:instore_merkle_slot st).
           let k' = stored_key st s in
           let v' = to_merkle_value (stored_value st s) in
           is_proper_desc k k' ∧
           Veritas.Verifier.Merkle.mv_points_to v' (desc_dir k k') k ∧
           in_store_bit st s (desc_dir k k') = true))
  ```
  ... or possibly directly say that s needs to contain the proving ancestor of k
* The intermediate-level state of every verifier is related to the corresponding spec-level state.

A sketch of the inductive step:
```
let inductive_step (itsl:il_hash_verifiable_log) (i:I.seq_index itsl)
  : Lemma (requires (let itsl_i = I.prefix itsl i in
                     let itsl_k_i = ilogS_to_logK itsl_i in
                     is_eac itsl_k_i ∧
                     forall_is_map itsl_i ∧
                     forall_merkle_inv itsl_i ∧
                     forall_vtls_rel itsl_i itsl_k_i))
          (ensures (let itsl_i1 = I.prefix itsl (i + 1) in
                    let itsl_k_i1 = ilogS_to_logK itsl_i1 in
                    hash_collision_gen ∨
                    (is_eac itsl_k_i1 ∧
                     forall_is_map itsl_i1 ∧
                     forall_merkle_inv itsl_i1 ∧
                     forall_vtls_rel itsl_i1 itsl_k_i1)))

  = let itsl_i1 = I.prefix itsl (i + 1) in
    let itsl_k_i1 = ilogS_to_logK itsl_i1 in
  
    let e = I.index itsl (i + 1)
    match e with
    | Get_S s k v -> 
        if is_eac itsl_k_i1
        then // easy
        else // re-use lemmas in Veritas.Verifier.EAC
    | Put_S s k v -> 
        if is_eac itsl_k_i1
        then // easy
        else // re-use lemmas in Veritas.Verifier.EAC   
    | AddM_S s (k,v) s' ->
        if is_eac itsl_k_i1
        then // s' stores the proving ancestor of k and s' either points to k or k is not in the store
             // - should be able to prove that is_map cannot become false (due to checks on in_store and evicted_to_blum bits)
        else // re-use lemmas in Veritas.Verifier.EAC
    | EvictM_S s s' ->
        if is_eac itsl_k_i1
        then // s' stores the proving ancestor of the key at s (k) and s' points to k
        else // re-use lemmas in Veritas.Verifier.EAC
    | AddB_S s (k,v) t j ->
        // hard case
    ...
```

Using this inductive step, we should be able to prove that either `itsl:il_hash_verifiable_log` can be converted into an evict-add consistent hash-verifiable spec log or there will be a hash collision, allowing us to prove the final property. 
