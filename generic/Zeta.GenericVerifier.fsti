module Zeta.GenericVerifier

open Zeta.Time

(*
 * Verifier built-in methods
 *
 * A verifier thread supports the following built-in methods that can be used
 * to (a) add records to its internal store (b) evict records from its internal
 * store; and (c) trigger epoch transitions.
 *
 * These are different from application methods that implement application-specific
 * state machine transitions.
 *)
type builtin_method =
  | AddM                    (* Add a record using Merkle verification *)
  | EvictM                  (* Evict a record, while protecting it using Merkle *)
  | AddB                    (* Add a record using Blum verification *)
  | EvictB                  (* Evict a record using Blum protection *)
  | EvictBM                 (* Evict a record added using Merkle using Blum protection *)
  | NextEpoch               (* Transition the verifier thread clock to next epoch *)
  | VerifyEpoch             (* *)

noeq type verifier_spec =
  | VSpec: vtls: Type0 ->                             (* type of thread local state *)
           valid: (vtls -> bool) ->                   (* valid function indicating if the thread is in a valid state *)
           clock: (v: vtls {valid v} -> timestamp) -> (* for valid states, the clock of the verifier thread *)
           verifier_spec
