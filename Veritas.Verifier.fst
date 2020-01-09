module Veritas.Verifier

open Veritas.Memory

(* Each entry of the verifier log *)
type verifier_log_entry = 
  | MemoryOp: o:memory_op -> verifier_log_entry
  | Add: a:addr -> v:payload -> verifier_log_entry
  | Evict: a:addr -> verifier_log_entry

type verifier_log = list verifier_log_entry

(* Verifier cache of a subset of memory *)
type verifier_cache = addr -> option payload 

(* Verifier state *)
(* TODO: Understand subtleties of noeq *)
noeq type verifier_state = 
  | Failed: verifier_state 
  | Valid: vc:verifier_cache -> verifier_state

let cache_apply (vc:verifier_cache) (o:memory_op): Tot verifier_cache =
  match o with
  | Read _ _ -> vc
  | Write a v -> (fun a' -> if a' = a then Some v else vc a')

let verifier_step (l:verifier_log_entry) (vs:verifier_state): Tot verifier_state = 
  if (Failed? vs) then Failed 
  else 
    let cache = (Valid?.vc vs) in 
    match l with 
    (* Memory operation *)
    | MemoryOp o -> 
        let cachedCell = cache (address_of o) in 
        (* If the address is not in our cache, verification fails *)
        if (None? cachedCell) then Failed        
        else (match o with
        (* For reads, the value read should correspond to the value in the cache *)
        | Read _ v -> if (v = (Some?.v cachedCell)) then vs else Failed
        (* For writes, update the cache to reflect the write *)
        | Write a v -> Valid (cache_apply cache o))
    | Add a v -> vs
    | Evict a -> vs
