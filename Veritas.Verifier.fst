module Veritas.Verifier

open FStar.Seq
open Veritas.Memory
open Veritas.Merkle

(* Each entry of the verifier log *)
type verifier_log_entry = 
  | MemoryOp: o:memory_op -> verifier_log_entry
  | Add: a:merkle_addr -> v:merkle_payload -> verifier_log_entry
  | Evict: a:merkle_addr -> verifier_log_entry

type verifier_log = list verifier_log_entry

(* Verifier cache of a subset of memory *)
type verifier_cache = (a:merkle_addr) -> option (p:merkle_payload {(is_merkle_leaf a /\ MkLeaf? p) \/ (~(is_merkle_leaf a) /\ MkInternal? p)}) 

(* Verifier state *)
(* TODO: Understand subtleties of noeq *)
noeq type verifier_state = 
  | Failed: verifier_state 
  | Valid: vc:verifier_cache -> verifier_state

let cache_apply (vc:verifier_cache) (o:memory_op): Tot verifier_cache =
  match o with
  | Read _ _ -> vc
  | Write a v -> (fun a' -> if a' = addr_to_merkle_leaf a then Some (MkLeaf v) else vc a')

let cache_add (vc:verifier_cache) (a:merkle_addr) (v:merkle_payload): Tot verifier_cache = 
  if is_merkle_leaf a && MkLeaf? v || not (is_merkle_leaf a) && MkInternal? v
  then fun a' -> if a' = a then Some v else vc a'
  else vc

let cache_evict (vc:verifier_cache) (a:merkle_addr): Tot verifier_cache = 
  fun a' -> if a' = a then None else vc a'

let verifier_step (l:verifier_log_entry) (vs:verifier_state): Tot verifier_state =
  if (Failed? vs) then Failed
  else
    let cache = (Valid?.vc vs) in
    match l with
    (* Memory operation *)
    | MemoryOp o ->
        let optPayload = cache (addr_to_merkle_leaf (address_of o)) in
        (* If the address is not in our cache, verification fails *)
        if (None? optPayload) then Failed
        else (
          let payload = Some?.v optPayload in
          match o with
          (* For reads, the value read should correspond to the value in the cache *)
          | Read _ v -> if v = MkLeaf?.value payload then vs else Failed            
          (* For writes, update the cache to reflect the write *)
          | Write a v -> Valid (cache_apply cache o))
    | Add a v -> Valid (cache_add cache a v)
    | Evict a -> Valid (cache_evict cache a)

