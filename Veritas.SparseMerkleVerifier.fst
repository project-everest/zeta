module Veritas.SparseMerkleVerifier

open FStar.Seq
open FStar.BitVector
open FStar.Classical
open Veritas.SeqAux
open Veritas.Memory
open Veritas.BinTree
open Veritas.BinTreePtr
open Veritas.MerkleAddr
open Veritas.SparseMerkle

//Allow the solver to unroll recursive functions at most once (fuel)
//Allow the solver to invert inductive definitions at most once (ifuel)
#push-options "--max_fuel 1 --max_ifuel 1 --initial_fuel 1 --initial_ifuel 1"

(*
 * The verifier consumes a log that consists of memory operations and
 * additional "proof" objects and returns success of failure; we prove
 * that if the verifier returns success, then the underlying memory
 * operations are read-write consistent
 *)

(* Each entry of the verifier log *)
type verifier_log_entry =
  | MemoryOp: o:memory_op -> verifier_log_entry
  | Add: a:merkle_addr -> v:merkle_payload -> a':merkle_addr -> verifier_log_entry
  | Evict: a:merkle_addr -> a':merkle_addr -> verifier_log_entry

type verifier_log = seq verifier_log_entry

(* index in the verifier log *)
type vl_index (l:verifier_log) = seq_index l

(* is the i'th operation an evict *)
let is_evict (l:verifier_log) (i:vl_index l): Tot bool =
  Evict? (index l i)

(* evicted address for an evict operation *)
let evict_addr (l:verifier_log) (i:vl_index l{is_evict l i}): Tot merkle_addr =
  Evict?.a (index l i)

(* ancestor recording the evicted nodes hashes *)
let evict_ancestor (l:verifier_log) (i:vl_index l{is_evict l i}): Tot merkle_addr =
  Evict?.a' (index l i)

(* is the ith operation an add *)
let is_add (l:verifier_log) (i:vl_index l) =
  Add? (index l i)

(* added address for an add operation *)
let add_addr (l:verifier_log) (i:vl_index l{is_add l i}): Tot merkle_addr =
  Add?.a (index l i)

(* added payload for an add operation *)
let add_payload (l:verifier_log) (i:vl_index l {is_add l i}): Tot merkle_payload =
  Add?.v (index l i)

let add_ancestor (l:verifier_log) (i:vl_index l {is_add l i}): Tot merkle_addr =
  Add?.a' (index l i)

(* is the ith operation a memory operation? *)
let is_memory_op (l:verifier_log) (i:vl_index l): Tot bool = MemoryOp? (index l i)

(* memory op for an memory_op index *)
let memory_op_at (l:verifier_log) (i:vl_index l{is_memory_op l i}) = MemoryOp?.o (index l i)

(* is the i'th operation a write operation *)
let is_write_op (l:verifier_log) (i:vl_index l): Tot bool =
  is_memory_op l i && Write? (memory_op_at l i)

(* written value for a write operation *)
let written_value (l:verifier_log) (i:vl_index l{is_write_op l i}): Tot payload =
  Write?.v (memory_op_at l i)

(* is the ith operation a read operation *)
let is_read_op (l:verifier_log) (i:vl_index l): Tot bool =
  is_memory_op l i && Read? (memory_op_at l i)

(* read value for a read operation *)
let read_value (l:verifier_log) (i:vl_index l{is_read_op l i}): Tot payload =
  Read?.v (memory_op_at l i)

(* Verifier cache of a subset of merkle_addr, merkle_payloads *)
type verifier_cache = (a:merkle_addr) -> option (merkle_payload_of_addr a)

(* Does the cache contain a merkle addr? *)
let cache_contains (vc:verifier_cache) (a:merkle_addr): Tot bool =
  Some? (vc a)

(* Lookup the payload of an address in cache *)
let cached_payload (cache:verifier_cache) (a:merkle_addr{cache_contains cache a}): 
  (merkle_payload_of_addr a) =
  Some?.v (cache a)

(*
 * Update the cache. This is a pure update function that requires
 * that cache contain an entry for the merkle address as a precondition
 *)
let cache_update (cache:verifier_cache)
                 (a:merkle_addr{cache_contains cache a})
                 (v:merkle_payload_of_addr a):
  Tot (cache':verifier_cache{cache_contains cache' a}) =
  fun a' -> if a' = a then Some v else cache a'

(*
 * Update the cache to reflect a memory write, which translates to updating
 * the leaf merkle node in the cache. This is a pure update function and we
 * require the cache to contain an entry for the merkle addr as a precondition
 *)
let cache_apply (cache:verifier_cache)
                (o:memory_op{Write? o &&
                             cache_contains cache (addr_to_merkle_leaf (address_of o))})
  : Tot (vc':verifier_cache{cache_contains vc' (addr_to_merkle_leaf (address_of o))}) =
  match o with
  | Read _ _ -> cache
  | Write a v -> cache_update cache (addr_to_merkle_leaf a) (SMkLeaf v)

(* Add a merkle_addr, payload to cache *)
let cache_add (cache:verifier_cache)
              (a:merkle_addr {not (cache_contains cache a)})
              (v:merkle_payload_of_addr a)
  : Tot (cache':verifier_cache {cache_contains cache' a}) =
  fun a' -> if a' = a then Some v else cache a'

(* Evict a merkle_addr from cache *)
let cache_evict (cache:verifier_cache)
                (a:merkle_addr{cache_contains cache a})
  : Tot verifier_cache =
  fun a' -> if a' = a then None else cache a'

(* Verifier state is the cache if valid *)
noeq type verifier_state =
  | Failed: verifier_state
  | Valid: vc:verifier_cache -> verifier_state

let lemma_proper_anc_implies_non_leaf (d: merkle_addr) (a: merkle_addr {is_proper_desc d a}):
  Lemma (not (is_merkle_leaf a)) 
  [SMTPat (is_proper_desc d a)]
  =
  lemma_proper_desc_depth_monotonic d a

let update_desc_hash (a:merkle_addr) (v:merkle_payload_of_addr a)
                     (d:merkle_addr {is_proper_desc d a}) (h:hash_value): Tot (merkle_payload_of_addr a) =
  if is_desc d (LeftChild a) then
    SMkInternal (Desc d h) (SMkInternal?.right v)
  else
    SMkInternal (SMkInternal?.left v) (Desc d h)

let is_empty_or_null (a:merkle_addr) (v:merkle_payload_of_addr a): Tot bool =
  if is_merkle_leaf a then Null? (SMkLeaf?.value v)
  else Empty? (SMkInternal?.left v) &&
       Empty? (SMkInternal?. right v)

let verifier_step (e:verifier_log_entry) (vs:verifier_state): Tot verifier_state =
  (* propagate failures *)
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
          | Read _ v -> if v = SMkLeaf?.value payload then vs else Failed
          (* For writes, update the cache to reflect the write *)
          | Write a v -> Valid (cache_apply cache o))
     | Add a v a' ->
         (* Check cache contains merkle addr a *)
         if cache_contains cache a then Failed
         (* Root is never added *)
         else if is_merkle_root a then Failed
         (* Check the payload type corresponds to leaf/internal ness of address a *)
         else if not (is_payload_of_addr a v) then Failed
         (* Check ancestor a' is in cache *)
         else if not (cache_contains cache a') then Failed
         (* check that a is a proper descendant of a' *)
         else if not (is_proper_desc a a') then Failed

         else (
           let v' = cached_payload cache a' in
           let c = desc_dir a a' in
           let dh' = desc_hash_dir c v' in
           let h = hashfn v in
           (* ancestor a' points to a *)
           if Desc? dh' && a = Desc?.a dh'  then
             (* check the hash and add a to cache if hash check passes *)
             if h = Desc?.h dh' then Valid (cache_add cache a v)
             else Failed
           (* if ancestor a' does not point to a, then a has to be empty *)
           else if not (is_empty_or_null a v) then Failed

           (* entire subtree l|r(a) subtree of a' empty *)
           else if Empty? dh' then
             (* if it is update a' to point to a *)
             let v'_upd = update_desc_hash a' v' a h in
             Valid (cache_add (cache_update cache a' v'_upd) a v)

           (* if a' points to some other addr, that addr has to be a desc of a *)
           else if not (is_proper_desc (Desc?.a dh') a) then Failed

           else
             let v_upd = update_desc_hash a v (Desc?.a dh') (Desc?.h dh') in
             let v'_upd = update_desc_hash a' v' a (hashfn v_upd) in
             Valid (cache_add (cache_update cache a' v'_upd) a v_upd)
         )
     | Evict a a' ->
         if not (cache_contains cache a && cache_contains cache a') then Failed
         else if is_merkle_root a then Failed
         else if not (is_proper_desc a a') then Failed
         else
           let c = desc_dir a a' in
           let v' = cached_payload cache a' in
           let v = cached_payload cache a in
           let h = hashfn v in
           let dh' = desc_hash_dir c v' in
           let v'_upd = update_desc_hash a' v' a h in
           if not (Empty? dh') && a = Desc?.a dh' then
             Valid (cache_evict (cache_update cache a' v'_upd) a)
           else Failed

(* Verifier for a given log, from a specified initial state *)
let rec verifier_aux (l:verifier_log) (init_vs:verifier_state): Tot verifier_state
  (decreases (length l)) =
  let n = length l in
  (* empty log *)
  if n = 0 then init_vs
  else
    let l' = prefix l (n - 1) in
    (* recurse *)
    let vs' = verifier_aux l' init_vs in
    let e' = index l (n - 1) in
    verifier_step e' vs'

(*
 * Initial payload for every merkle node for init memory where each address
 * contains Null
 *)
let init_payload (a:merkle_addr): Tot (merkle_payload_of_addr a) =
    if is_merkle_leaf a then
      SMkLeaf Null
    else
      SMkInternal Empty Empty

(* Initial cache contains only the merkle root *)
let init_cache:verifier_cache =
  fun a -> if is_merkle_root a then
           Some (init_payload a)
         else None

(* Verifier for a log from the initial state *)
let verifier (l:verifier_log): Tot verifier_state =
  verifier_aux l (Valid init_cache)

let initial_verifier_state
  : verifier_state
  = Valid init_cache

(* Verifier for a log from a given state *)
let verifier_incremental (l:verifier_log) (v:verifier_state)
  : Tot verifier_state
  = verifier_aux l v

