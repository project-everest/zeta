(* 
 * MerkleVerifier 
 * 
 * Use Merkle tree ideas to design a memory verifier 
 *)
module Veritas.MerkleVerifier

open FStar.Seq
open Veritas.Memory
open Veritas.Merkle

(* 
 * The verifier consumes a log that consists of memory operations and 
 * additional "proof" objects and returns success of failure; we prove
 * that if the verifier returns success, then the underlying memory 
 * operations are read-write consistent 
 *)

(* Each entry of the verifier log *)
type verifier_log_entry = 
  | MemoryOp: o:memory_op -> verifier_log_entry
  | Add: a:merkle_addr -> v:merkle_payload -> verifier_log_entry
  | Evict: a:merkle_addr -> verifier_log_entry

type verifier_log = seq verifier_log_entry

(* Verifier cache of a subset of merkle_addr, merkle_payloads *)
type verifier_cache = (a:merkle_addr) -> option (merkle_payload_of_addr a)

(* Does the cache contain a merkle addr? *)
let cache_contains (vc:verifier_cache) (a:merkle_addr): Tot bool = 
  Some? (vc a)

(* 
 * Update the cache to reflect a memory write, which translates to updating 
 * the leaf merkle node in the cache. This is a pure update function and we 
 * require the cache to contain an entry for the merkle addr as a precondition
 *)
let cache_apply (o:memory_op{Write? o}) 
                (vc:verifier_cache{cache_contains vc (addr_to_merkle_leaf (address_of o))})
  : Tot (vc':verifier_cache{cache_contains vc' (addr_to_merkle_leaf (address_of o))}) =
  match o with
  | Read _ _ -> vc
  | Write a v -> (fun a' -> if a' = addr_to_merkle_leaf a then Some (MkLeaf v) else vc a')

(* Add a merkle_addr, payload to cache *)
let cache_add (a:merkle_addr) (v:merkle_payload_of_addr a) (vc:verifier_cache)
  : Tot verifier_cache = 
  fun a' -> if a' = a then Some v else vc a'

(* Evict a merkle_addr from cache *)
let cache_evict (a:merkle_addr) (vc:verifier_cache{cache_contains vc a})
  : Tot verifier_cache = 
  fun a' -> if a' = a then None else vc a'

(* Verifier state is the cache if valid *)
(* TODO: Understand subtleties of noeq *)
noeq type verifier_state = 
  | Failed: verifier_state 
  | Valid: vc:verifier_cache -> verifier_state

(* Each step of the verifier *)
let verifier_step (e:verifier_log_entry) (vs:verifier_state): Tot verifier_state =
  if (Failed? vs) then Failed
  else
    let cache = (Valid?.vc vs) in
    match e with
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
          | Write a v -> Valid (cache_apply o cache))
    | Add a v -> 
        (* TODO: is there a more concise syntax for (instance-of (merkle_payload_of_addr a) v)? *)
        if (is_merkle_leaf a && MkLeaf? v || not (is_merkle_leaf a) && MkInternal? v) then           
          Valid (cache_add a v cache)
        else 
          Failed
    | Evict a -> 
        if cache_contains cache a then
          Valid (cache_evict a cache)
        else
          Failed

(* Verifier *)
let rec verifier_aux (l:verifier_log) (vs:verifier_state): Tot verifier_state 
  (decreases (length l)) =
  let n = length l in
  if n = 0 then vs
  else
    let l' = slice l 0 (n - 1) in
    let vs' = verifier_aux l' vs in
    let e' = index l (n - 1) in 
    verifier_step e' vs'

(* Initial cache contains only the merkle root *)
let init_cache:verifier_cache = 
  fun a -> if is_merkle_root a then 
           Some (merklefn a init_memory)
         else None  

let verifier (l:verifier_log): Tot verifier_state = 
  verifier_aux l (Valid init_cache)

