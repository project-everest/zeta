(* 
 * MerkleVerifier 
 * 
 * Use Merkle tree ideas to design a memory verifier 
 *)
module Veritas.MerkleVerifier

open FStar.Seq
open FStar.Classical
open Veritas.SeqLast
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
        if is_merkle_root a then Failed
        else if cache_contains cache a then
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

type vl_index (l:verifier_log) = seq_index l

let is_evict (l:verifier_log) (i:vl_index l): Tot bool =
  Evict? (index l i)

let evict_addr (l:verifier_log) (i:vl_index l{is_evict l i}): Tot merkle_addr = 
  Evict?.a (index l i)

let verifiable (l:verifier_log): Tot bool = 
  Valid? (verifier l)

type verifiable_log = l:verifier_log{verifiable l}

let rec verifiable_implies_prefix_verifiable (l:verifiable_log) (i:nat{i <= length l}):
  Lemma (requires (True))
        (ensures (verifiable (slice l 0 i)))
        (decreases (length l)) = 
  let n = length l in
  if n = 0 then ()
  else if i = n then ()
  else verifiable_implies_prefix_verifiable (slice l 0 (n - 1)) i    

let evict_payload (l:verifiable_log) (i:vl_index l{is_evict l i}): 
  Tot (merkle_payload_of_addr (evict_addr l i)) =
  verifiable_implies_prefix_verifiable l (i + 1);
  verifiable_implies_prefix_verifiable l i;
  let a = evict_addr l i in
  let l'' = slice l 0 i in
  let vs'' = verifier l'' in    
  Some?.v ((Valid?.vc vs'') a)

let is_evict_of_addr (a:merkle_addr) (e:verifier_log_entry) = 
  Evict? e && Evict?.a e = a

let last_evict (l:verifier_log) (a:merkle_addr):
  Tot (option (i:vl_index l{is_evict_of_addr a (index l i)})) = 
  let f = is_evict_of_addr a in
  let optwi = last_index l f in
  if None? optwi then None
  else 
    let wi = Some?.v optwi in
    (last_index_correct1 l f; Some wi)

let is_add (l:verifier_log) (i:vl_index l) = 
  Add? (index l i)

let add_addr (l:verifier_log) (i:vl_index l{is_add l i}): Tot merkle_addr = 
  Add?.a (index l i)

let add_payload (l:verifier_log) (i:vl_index l {is_add l i}): Tot merkle_payload =
  Add?.v (index l i)

let prev_evict_of_add (l:verifier_log) (i:vl_index l{is_add l i}):
  Tot (option (j:vl_index l{j < i && is_evict l j && add_addr l i = evict_addr l j})) = 
  let l' = slice l 0 i in
  let a = add_addr l i in 
  let optj = last_evict l' a in
  if None? optj then None
  else
    let j = Some?.v optj in 
    (
      lemma_len_slice l 0 i;
      lemma_index_slice l 0 i j;
      Some j
    )

let has_prev_evict (l:verifier_log) (i:vl_index l{is_add l i}): Tot bool = 
  Some? (prev_evict_of_add l i)

let has_no_prev_evict (l:verifier_log) (i:vl_index l{is_add l i}): Tot bool =
  None? (prev_evict_of_add l i)

let rec project_memory_log (l:verifier_log): 
  Tot memory_op_log (decreases (length l)) = 
  let n = length l in
  if n = 0 then empty
  else 
    let l' = slice l 0 (n - 1) in
    let ml' = project_memory_log l' in
    let e = index l (n - 1) in
    match e with
    | MemoryOp o -> append ml' (create 1 o)
    | _ -> ml'

type evict_add_consistent (l:verifiable_log) = 
  u:unit{forall (i:vl_index l). 
    is_add l i /\ is_merkle_leaf (add_addr l i) ==> 
    has_no_prev_evict l i && add_payload l i = MkLeaf Null \/
    has_prev_evict l i && 
    add_payload l i = evict_payload l (Some?.v (prev_evict_of_add l i))
    }

let cache_at_end (l:verifiable_log): Tot verifier_cache = 
  Valid?.vc (verifier l)

let last_write_value_or_null (l:verifiable_log) (ma:merkle_leaf_addr): Tot merkle_payload =
  let ml = project_memory_log l in
  let a = merkle_leaf_to_addr ma in
  if has_some_write ml a then
    MkLeaf (last_write_value ml a)
  else
    MkLeaf Null
      
let rec eac_implies_cache_is_last_write (l:verifiable_log) (a:merkle_leaf_addr):
  Lemma (requires (evict_add_consistent l))
        (ensures (cache_contains (cache_at_end l) a ==> 
                  Some?.v ((cache_at_end l) a) = last_write_value_or_null l a))
        (decreases (length l)) = admit()

let rec eac_implies_read_last_write (l:verifiable_log):
  Lemma (requires (evict_add_consistent l))
        (ensures (

let rec evict_add_consistency_implies_rw_consistency (l:verifiable_log):
  Lemma (requires (forall (i:vl_index l). 
                     is_add l i /\ is_merkle_leaf (add_addr l i)  ==> 
                       has_no_prev_evict l i && add_payload l i = MkLeaf Null \/
                       has_prev_evict l i && 
                       add_payload l i = evict_payload l (Some?.v (prev_evict_of_add l i))))
        (ensures (rw_consistent (project_memory_log l)))
        (decreases (length l)) = 
  let n = length l in
  if n = 0 then ()
  else 
    let l' = slice l 0 (n - 1) in
    let e = index l (n - 1) in
    let aux (i:vl_index l'):
      Lemma (is_add l' i /\ is_merkle_leaf (add_addr l' i) ==>
             has_no_prev_evict l' i && add_payload l' i = MkLeaf Null \/
             has_prev_evict l' i && 
             add_payload l' i = evict_payload l (Some?.v (prev_evict_of_add l' i))) = admit () in
    forall_intro aux; 
    verifiable_implies_prefix_verifiable l (n - 1);
    evict_add_consistency_implies_rw_consistency l';
    match e with
    | 
    admit()
  
