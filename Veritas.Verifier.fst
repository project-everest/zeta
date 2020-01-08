module Veritas.Verifier

open Veritas.Memory

(* Each entry of the verifier log *)
type verifier_log_entry = 
  | MemoryOp: o:memory_op -> verifier_log_entry
  | Add: a:addr -> v:payload -> verifier_log_entry
  | Evict: a:addr -> verifier_log_entry

type verifier_log = list verifier_log_entry

(* Verifier state: payload for some subset of addresses *)
type verifier_state = addr -> option payload

noeq type verifier_response = 
  | Failure: verifier_response
  | Success: vs:verifier_state -> verifier_response

