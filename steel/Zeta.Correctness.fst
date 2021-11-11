module Zeta.Correctness
open Zeta.Steel.ThreadStateModel

// There's a bunch of old code/proofs in
// to_be_restored/Veritas.SingleThreadSimulation
// that could help with this proof
// The main lemma there, related_entries, says that if you
// start the Veritas.Steel.ThreadStateModel and
// Intermediate.Verifier in related stats
// and you run them on related log entries
// then they end in related states.
// But, those definitions are stale

assume
val seq_consistent (logs:all_logs) (eid:epoch_id)
  : prop

assume
val merkle_hash_collision : Type0

assume
val multiset_hash_collision : Type0

(* the definition of epoch_is_certified may need to be adjusted ... *)
let main_lemma (logs:all_logs)
               (eid:epoch_id { epoch_is_certified logs eid })
               (_ : squash (~ (seq_consistent logs eid) ))
  : Tot (either merkle_hash_collision multiset_hash_collision)
  = admit()
