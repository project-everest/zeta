module Veritas.SparseMerkleVerifier

open FStar.Seq
open FStar.BitVector
open FStar.Classical
open Veritas.SeqAux
open Veritas.Memory
open Veritas.Merkle

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
  | Add: a:merkle_addr -> v:sp_merkle_payload -> a':merkle_addr -> verifier_log_entry
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
let add_payload (l:verifier_log) (i:vl_index l {is_add l i}): Tot sp_merkle_payload =
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
type verifier_cache = (a:merkle_addr) -> option (sp_merkle_payload_of_addr a)

(* Does the cache contain a merkle addr? *)
let cache_contains (vc:verifier_cache) (a:merkle_addr): Tot bool =
  Some? (vc a)

(* Lookup the payload of an address in cache *)
let cached_payload (cache:verifier_cache) (a:merkle_addr{cache_contains cache a}): Tot (sp_merkle_payload_of_addr a) =
  Some?.v (cache a)

(*
 * Update the cache. This is a pure update function that requires
 * that cache contain an entry for the merkle address as a precondition
 *)
let cache_update (cache:verifier_cache)
                 (a:merkle_addr{cache_contains cache a})
                 (v:sp_merkle_payload_of_addr a):
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
              (v:sp_merkle_payload_of_addr a)
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

let get_desc_hash (a: merkle_non_root_addr)
                  (a':merkle_addr {is_proper_desc a a'})
                  (v': sp_merkle_payload_of_addr a'):
  Tot (dh:desc_hash) =
  if is_desc a (LeftChild a') then
    SMkInternal?.left v'
  else
    SMkInternal?.right v'

let update_desc_hash (a:merkle_addr) (v:sp_merkle_payload_of_addr a)
                     (d:merkle_addr {is_proper_desc d a}) (h:hash_value): Tot (sp_merkle_payload_of_addr a) =
  if is_desc d (LeftChild a) then
    SMkInternal (Desc d h) (SMkInternal?.right v)
  else
    SMkInternal (SMkInternal?.left v) (Desc d h)

let is_empty_or_null (a:merkle_addr) (v:sp_merkle_payload_of_addr a): Tot bool =
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
         else if not (is_sp_payload_of_addr a v) then Failed
         (* Check ancestor a' is in cache *)
         else if not (cache_contains cache a') then Failed
         (* check that a is a proper descendant of a' *)
         else if not (is_proper_desc a a') then Failed

         else (
           let v' = cached_payload cache a' in
           let dh' = get_desc_hash a a' v' in
           let h = hashfn_sp v in
           (* ancestor a' stores the address a and its hash *)
           if not (Empty? dh') && a = Desc?.a dh' then
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
             let v'_upd = update_desc_hash a' v' a (hashfn_sp v_upd) in
             Valid (cache_add (cache_update cache a' v'_upd) a v_upd)
         )
     | Evict a a' ->
         if not (cache_contains cache a && cache_contains cache a') then Failed
         else if is_merkle_root a then Failed
         else if not (is_proper_desc a a') then Failed
         else
           let v' = cached_payload cache a' in
           let v = cached_payload cache a in
           let h = hashfn_sp v in
           let dh' = get_desc_hash a a' v' in
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
let init_payload (a:merkle_addr): Tot (sp_merkle_payload_of_addr a) =
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

(* Does the verifier return Valid (success) for this log *)
let verifiable (l:verifier_log): Tot bool =
  Valid? (verifier l)

(* Refinement type of logs that are verifiable *)
type verifiable_log = l:verifier_log{verifiable l}

(* If a log is verifiable, then each prefix of the log is also verifiable *)
let rec lemma_verifiable_implies_prefix_verifiable (l:verifiable_log) (i:nat{i <= length l}):
  Lemma (requires (True))
        (ensures (verifiable (prefix l i)))
        (decreases (length l))
        [SMTPat (prefix l i)]
        =
  let n = length l in
  if n = 0 then ()
  else if i = n then ()
  else
    lemma_verifiable_implies_prefix_verifiable (prefix l (n - 1)) i


(* is this log entry, an evict of a specified address *)
let is_evict_of_addr (a:merkle_addr) (e:verifier_log_entry) =
  Evict? e && Evict?.a e = a

(* Does this log have some evict entry for address a *)
let has_some_evict (l:verifier_log) (a:merkle_addr) = exists_sat_elems (is_evict_of_addr a) l

(* Index of the last evict entry *)
let last_evict_idx (l:verifier_log) (a:merkle_addr{has_some_evict l a}) =
  last_index (is_evict_of_addr a) l

(* Is this an add operation on address a *)
let is_add_of_addr (a:merkle_addr) (e:verifier_log_entry) =
  Add? e && Add?.a e = a

(* Does thie log have some add entry for address a *)
let has_some_add (l:verifier_log) (a:merkle_addr) = exists_sat_elems (is_add_of_addr a) l

(* Index of the last add operation *)
let last_add_idx (l:verifier_log) (a:merkle_addr{has_some_add l a}) =
  last_index (is_add_of_addr a) l

(* Is this log entry a write to address a *)
let is_write_to_addr (a:merkle_leaf_addr) (e:verifier_log_entry) =
  MemoryOp? e && is_write_to_addr (merkle_leaf_to_addr a) (MemoryOp?.o e)

(* Does this log have some write to address a *)
let has_some_write (l:verifiable_log) (a:merkle_leaf_addr) = exists_sat_elems (is_write_to_addr a) l

(* Index of last write to address a *)
let last_write_idx (l:verifiable_log) (a:merkle_leaf_addr{has_some_write l a}) =
  last_index (is_write_to_addr a) l

(* State of the cache after processing log l *)
let cache_at_end (l:verifiable_log): Tot verifier_cache =
  Valid?.vc (verifier l)

(*
 * We want to prove that if the verifier returns Valid for a log l, then the
 * read-write operations in log l are rw-consistent unless there is a hash collision.
 * To prove this, we develop a notion of evict-add consistency:
 *
 * A log is evict-add consistent, if every add sees the payload of the most recent evict
 * to the same address or some initial value if there has been no previous evict
 *
 * We prove (1) evict-add consistency implies rw-consistency (2) a verifiable log that is
 * not evict-add consistent implies a hash collision (that we construct)
 *)

(* payload of an evict operation *)
let evict_payload (l:verifiable_log) (i:vl_index l{is_evict l i}):
  Tot (sp_merkle_payload_of_addr (evict_addr l i)) =
  let a = evict_addr l i in
  let vs'' = verifier (prefix l i) in
  lemma_prefix_index l (i + 1) i;
  Some?.v ((Valid?.vc vs'') a)

(*
 * for a given address a, the last evict payload or init_payload if
 * there exists no evicts for add
 *)
let last_evict_value_or_init (l:verifiable_log) (a:merkle_addr):
  Tot (sp_merkle_payload_of_addr a) =
  if has_some_evict l a then
    evict_payload l (last_evict_idx l a)
  else
    init_payload a

(* evict-add consistency (eac) for a verifiable log *)
type evict_add_consistent (l:verifiable_log) = forall (i:vl_index l).
    is_add l i  ==>
    add_payload l i = last_evict_value_or_init (prefix l i) (add_addr l i)

(* refinement of verifiable logs that are evict-add consistent *)
type eac_log  = l:verifiable_log {evict_add_consistent l}

(* Lemma: prefix of evict-add-consistent log is evict-add-consistent *)
let lemma_eac_prefix (l:eac_log) (i:nat{i <= length l}):
  Lemma (requires (True))
        (ensures (evict_add_consistent (prefix l i)))
        [SMTPat (prefix l i)]
        =
  let l' = prefix l i in
  let aux (j:vl_index l'):
    Lemma (requires is_add l' j)
          (ensures add_payload l' j = last_evict_value_or_init (prefix l' j) (add_addr l' j))
          [SMTPat(is_add l' j)] = ()
  in
  ()

(* 
 * return the first index i, such that prefix of l of length i is evict add consistent 
 * and prefix of length (i + 1) is not
 *)
let rec search_first_non_eac_prefix (l:verifiable_log):
  Tot (i:nat{i <= length l /\
            evict_add_consistent (prefix l i) /\
            (i < length l ==> (is_add l i &&
                               add_payload l i <> last_evict_value_or_init (prefix l i)
                                                                          (add_addr l i)))})
  (decreases (length l)) =
  let n = length l in
  if n = 0 then 0
  else
    let l' = prefix l (n - 1) in
    let i' = search_first_non_eac_prefix l' in
    if i' < n - 1 then i'
    else
      if is_add l (n - 1) &&
         add_payload l (n - 1) <> last_evict_value_or_init l' (add_addr l (n - 1)) then
         n - 1
      else
        let aux (i:vl_index l)
          : Lemma
            (requires is_add l i)
            (ensures add_payload l i = last_evict_value_or_init (prefix l i) (add_addr l i))
            [SMTPat (is_add l i)]
          =
          if i = n - 1 then ()
          else (
            let l_i = prefix l i in
            if not (is_add l i) then ()
            else (
              assert (is_add l' i  ==>
                     add_payload l' i = last_evict_value_or_init (prefix l' i) (add_addr l' i));
              ()
            )
          )
       in
       n

(* Identify the smallest non-evict-add consistent prefix *)
let first_non_eac_prefix (l:verifiable_log {~(evict_add_consistent l)})
  : Tot (i:seq_index l{evict_add_consistent (prefix l i) /\
                       (is_add l i && 
                        add_payload l i <> last_evict_value_or_init (prefix l i)
                                                                   (add_addr l i))}) = 
  search_first_non_eac_prefix l

(* evict add consistent is computable *)
let is_evict_add_consistent (l:verifiable_log): 
  Tot (b:bool{b <==> evict_add_consistent l}) = 
  search_first_non_eac_prefix l = length l

(* 
 * for a verifiable log l, every merkle addr is associated with an ancestor identified below 
 * - the smallest ancestor who has been added so far - as verifying ancestor. The verifying 
 * ancestor is the one that will validate address a during Add's
 *)
let rec verifying_ancestor (l:verifiable_log) (a:merkle_non_root_addr): 
  Tot (a':merkle_addr{is_proper_desc a a'}) 
  (decreases (length l)) = 
  let n = length l in
  if n = 0 then (
    lemma_root_is_univ_ancestor a;
    merkle_root
  )
  else 
    let l' = prefix l (n - 1) in
    let va' = verifying_ancestor l' a in
    if is_add l (n - 1) then
      let a' = add_addr l (n - 1) in
      if is_proper_desc a a' && is_proper_desc a' va' then a'
      else va'
    else va'

let points_to (d:merkle_addr) (a: merkle_addr{is_proper_desc d a}) (v:sp_merkle_payload_of_addr a) : Tot bool = 
  let dh = get_desc_hash d a v in
  not (Empty? dh) && d = Desc?.a dh

(* 
 * If the verifying ancestor of 'a' is in the cache and address a has been added at least once, then 
 * the ancestor payload points to a 
 *)
let rec lemma_verifying_ancestor_correct 
  (l:verifiable_log) 
  (a:merkle_non_root_addr{has_some_add l a /\ 
                          cache_contains (cache_at_end l) (verifying_ancestor l a) /\
                          not (points_to a (verifying_ancestor l a) (cached_payload (cache_at_end l) (verifying_ancestor l a)))})
  : Tot hash_collision_sp (decreases (length l)) = 
  let cache = cache_at_end l in
  let va = verifying_ancestor l a in
  let pva = cached_payload cache va in
  let n = length l in 
  (* contradiction since l has some add of a *)
  if n = 0 then SCollision (SMkLeaf Null) (SMkLeaf Null)
  
  else 
    let l' = prefix l (n - 1) in
    let e = index l (n - 1) in
    match e with 
    | _ ->
    admit()
                                                                 
