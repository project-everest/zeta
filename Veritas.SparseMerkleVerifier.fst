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

let is_add_with_anc (a:merkle_addr) (e:verifier_log_entry) = 
  Add? e && Add?.a' e = a

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
 * Lemma: if there is a memory operation at index i, then cache at that position
 * contains the address touched by the operation 
 *)
let lemma_memop_requires_cache (l:verifiable_log) (i:vl_index l):
  Lemma (requires (is_memory_op l i))
        (ensures  (cache_contains (cache_at_end (prefix l i)) 
                                  (addr_to_merkle_leaf (address_of (memory_op_at l i))))) =
  lemma_verifiable_implies_prefix_verifiable l (i + 1)

(*
 * Lemma: An evict operation requires the cache to contain the evicted address 
 *)
let lemma_evict_requires_cache (l:verifiable_log) (i:vl_index l):
  Lemma (requires (is_evict l i))
        (ensures  (cache_contains (cache_at_end (prefix l i)) (evict_addr l i))) = 
  lemma_verifiable_implies_prefix_verifiable l (i + 1)

(* Lemma: add operation requires cache not to contain the added address *)
let lemma_add_requires_not_cached (l:verifiable_log) (i:vl_index l):
  Lemma (requires (is_add l i))
        (ensures (not (cache_contains (cache_at_end (prefix l i)) (add_addr l i)))) = 
  lemma_verifiable_implies_prefix_verifiable l (i + 1)
        
(*
 * Lemma: merkle root is never added
 *)
let lemma_root_never_added (l:verifiable_log) (i:vl_index l):
  Lemma (requires (is_add l i))
        (ensures (not (is_merkle_root (add_addr l i)))) = 
  lemma_verifiable_implies_prefix_verifiable l (i + 1)

(* Lemma: merkle root never evicted *)
let lemma_root_never_evicted (l:verifiable_log) (i:vl_index l):
  Lemma (requires (is_evict l i))
        (ensures (not (is_merkle_root (evict_addr l i)))) = 
  lemma_verifiable_implies_prefix_verifiable l (i + 1)

(* does the log entry e change the addresses being cached *)
let changes_caching (a:merkle_addr) (e:verifier_log_entry): Tot bool = 
  match e with
  | Add a' _ _ -> a = a'
  | Evict a' _ -> a = a'
  | _ -> false

(* if the last entry does not add/evict a, the cache containment of a is unchanged *)
let lemma_changes_caching (l:verifiable_log {length l > 0}) (a:merkle_addr):
  Lemma (requires (not (changes_caching a (index l (length l - 1)))))
        (ensures (cache_contains (cache_at_end l) a = 
                  cache_contains (cache_at_end (prefix l (length l - 1))) a)) = 
  ()

(* 
 * If the cache contains an address a (non root), then the last add/evict operation 
 * is an add 
 *)
let rec lemma_cache_contains_implies_last_add_before_evict (l:verifiable_log) (a:merkle_non_root_addr):
  Lemma (requires (cache_contains (cache_at_end l) a))
        (ensures (has_some_add l a /\
                  (has_some_evict l a ==> last_evict_idx l a < last_add_idx l a)))
        (decreases (length l)) 
        = 
  let n = length l in
  let cache = cache_at_end l in
  if n = 0 then ()
  else
    let l' = prefix l (n - 1) in
    let cache' = cache_at_end l' in
    let e = index l (n - 1) in

    if not (changes_caching a e) then (
      (* induction on l' *)
      lemma_cache_contains_implies_last_add_before_evict l' a;

      (* induction provides l' and therefore l has some add *)
      assert (has_some_add l a);

      (* since e is not and add a, the last add index remains unchanged from l' to l *)
      lemma_last_index_last_elem_nsat (is_add_of_addr a) l;
      lemma_last_index_prefix (is_add_of_addr a) l (n - 1);
      assert (last_add_idx l a = last_add_idx l' a);

      (* since e is not an evict a, the last evict index remains unchanged from l' to l *)
      lemma_last_index_last_elem_nsat (is_evict_of_addr a) l;
      if has_some_evict l a then 
        lemma_last_index_prefix (is_evict_of_addr a) l (n - 1)
      else ()
    )
    else if is_add_of_addr a e then
      lemma_last_index_correct2 (is_add_of_addr a) l (n - 1) 
    else ()    

(* 
 * If the cache does not contain an address a, then the last add/evict operation
 * is an evict
 *)
let rec lemma_not_contains_implies_last_evict_before_add (l:verifiable_log) (a:merkle_non_root_addr):
  Lemma (requires (not (cache_contains (cache_at_end l) a)))
        (ensures (has_some_add l a ==> has_some_evict l a /\ last_evict_idx l a > last_add_idx l a))
        (decreases (length l)) = 
  let n = length l in
  let cache = cache_at_end l in
  if n = 0 then ()
  else
    let l' = prefix l (n - 1) in
    let cache' = cache_at_end l' in
    let e = index l (n - 1) in
    if not (changes_caching a e) then (
      (* apply induction on l' *)
      lemma_not_contains_implies_last_evict_before_add l' a;

      (* e is neither add or evict *)
      lemma_last_index_last_elem_nsat (is_add_of_addr a) l;
      lemma_last_index_last_elem_nsat (is_evict_of_addr a) l;

      (* nothing to prove if l does not have an add *)
      if (not (has_some_add l a)) then ()
      else (
        (* last add-a of l and l' identical *)
        lemma_last_index_prefix (is_add_of_addr a) l (n - 1);
        assert (last_add_idx l a = last_add_idx l' a);

        (* last evict-a of l and l' identical *)
        lemma_exists_prefix_implies_exists (is_evict_of_addr a) l (n - 1);
        lemma_last_index_prefix (is_evict_of_addr a) l (n - 1);

        (* induction hypothesis and previous two identities implies post-condition *)
        ()
      )
    )
    else if is_evict_of_addr a e then
      lemma_last_index_correct2 (is_evict_of_addr a) l (n - 1)
    else ()

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
  Tot (merkle_payload_of_addr (evict_addr l i)) =
  let a = evict_addr l i in
  let vs'' = verifier (prefix l i) in
  lemma_prefix_index l (i + 1) i;
  Some?.v ((Valid?.vc vs'') a)

(*
 * for a given address a, the last evict payload or init_payload if
 * there exists no evicts for add
 *)
let last_evict_value_or_init (l:verifiable_log) (a:merkle_addr):
  Tot (merkle_payload_of_addr a) =
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

(* eac_payload of an address - cached payload if it is cached or the last evict value or init value *)
let eac_payload (l:eac_log) (a:merkle_addr): (merkle_payload_of_addr a) = 
  let cache = cache_at_end l in
  if cache_contains cache a then 
    cached_payload cache a
  else 
    last_evict_value_or_init l a

let updates_cache (a:merkle_non_leaf_addr) (e:verifier_log_entry): bool = 
  match e with
  | Add a1 _ a2 -> a1 = a || a2 = a
  | Evict a1 a2 -> a1 = a || a2 = a
  | _ -> false

let hprefix (l:eac_log{length l > 0}): eac_log = 
  let n = length l in
  prefix l (n - 1)

let telem (l:verifier_log{length l > 0}): verifier_log_entry = 
  index l (length l - 1)

let lemma_eac_payload_empty_or_points_to_desc_caseA
  (l:eac_log{length l > 0})
  (a:merkle_non_leaf_addr)
  (c:bin_tree_dir):
  Lemma (requires (not (updates_cache a (telem l)) /\ 
                   (Empty? (desc_hash_dir c (eac_payload (hprefix l) a)) \/
                    is_desc (Desc?.a (desc_hash_dir c (eac_payload (hprefix l) a))) (child c a))))
        (ensures (Empty? (desc_hash_dir c (eac_payload l a)) \/
                  is_desc (Desc?.a (desc_hash_dir c (eac_payload l a))) (child c a))) =
  let n = length l in
  let cache = cache_at_end l in
  if cache_contains cache a then ()
  else 
    if has_some_evict l a then (
      lemma_last_index_last_elem_nsat (is_evict_of_addr a) l;
      lemma_last_index_prefix (is_evict_of_addr a) l (n - 1)      
    )
    else lemma_not_exists_prefix (is_evict_of_addr a) l (n - 1)

let lemma_eac_payload_empty_or_points_to_desc_caseB
  (l:eac_log{length l > 0})
  (a:merkle_non_leaf_addr)
  (c:bin_tree_dir):
  Lemma (requires (is_add_of_addr a (telem l) /\ 
                   (Empty? (desc_hash_dir c (eac_payload (hprefix l) a)) \/
                    is_desc (Desc?.a (desc_hash_dir c (eac_payload (hprefix l) a))) (child c a))))
        (ensures (Empty? (desc_hash_dir c (eac_payload l a)) \/
                  is_desc (Desc?.a (desc_hash_dir c (eac_payload l a))) (child c a))) =
  let l' = hprefix l in
  let e = telem l in
  let cache' = cache_at_end l' in
  match e with
  | Add a v a2 -> 
    let v2 = cached_payload cache' a2 in
    let c2 = desc_dir a a2 in
    let dh2 = desc_hash_dir c2 v2 in
    if Desc? dh2 && a = Desc?.a dh2 then ()
    else if Empty? dh2 then ()
    else
      let c' = desc_dir (Desc?.a dh2) a in
      if c' = c then ()
      else ()                  

let lemma_eac_payload_empty_or_points_to_desc_caseC
  (l:eac_log{length l > 0})
  (a:merkle_non_leaf_addr)
  (c:bin_tree_dir):
  Lemma (requires (is_add_with_anc a (telem l) /\ 
                   (Empty? (desc_hash_dir c (eac_payload (hprefix l) a)) \/
                    is_desc (Desc?.a (desc_hash_dir c (eac_payload (hprefix l) a))) (child c a))))
        (ensures (Empty? (desc_hash_dir c (eac_payload l a)) \/
                  is_desc (Desc?.a (desc_hash_dir c (eac_payload l a))) (child c a))) =
  let l' = hprefix l in
  let e = telem l in
  let cache' = cache_at_end l' in
  let cache = cache_at_end l in
  match e with
  | Add a1 v1 a -> 
    let v' = cached_payload cache' a in        
    let c' = desc_dir a1 a in
    let dh' = desc_hash_dir c' v' in
    if Desc? dh' && a1 = Desc?.a dh' then ()            
    else if c = c' then (
      let v = cached_payload cache a in
      let dh = desc_hash_dir c v in          
      assert (Desc?.a dh = a1);
      ()
    )
    else ()
 
let rec lemma_eac_payload_empty_or_points_to_desc
  (l:eac_log)
  (a:merkle_non_leaf_addr)
  (c:bin_tree_dir):
  Lemma (requires (True))
        (ensures (Empty? (desc_hash_dir c (eac_payload l a)) \/
                  is_desc (Desc?.a (desc_hash_dir c (eac_payload l a))) (child c a)))
        (decreases (length l))
  =
  let n = length l in
  let cache = cache_at_end l in
  if n = 0 then ()
  else
    let l' = prefix l (n - 1) in
    let e = index l (n - 1) in
    let cache' = cache_at_end l' in
    lemma_eac_payload_empty_or_points_to_desc l' a c;    
    if not (updates_cache a e) then 
      lemma_eac_payload_empty_or_points_to_desc_caseA l a c    
    else
      match e with    
      | Add a1 v1 a2 -> 
        if a1 = a then 
          lemma_eac_payload_empty_or_points_to_desc_caseB l a c        
        else 
          lemma_eac_payload_empty_or_points_to_desc_caseC l a c         
      | Evict a1 a2 -> 
        if a1 = a then (
          lemma_last_index_last_elem_sat (is_evict_of_addr a) l;
          assert(eac_payload l a = cached_payload cache' a);
          ()
        )
        else (
          assert(a2 = a);
          let c' = desc_dir a1 a in
          let dh' = desc_hash_dir c' (cached_payload cache' a) in
          let dh = desc_hash_dir c (cached_payload cache a) in
          if c' = c then (
            assert (Desc? dh && Desc?.a dh = a1);
            ()
          )
          else (
            assert (desc_hash_dir c (cached_payload cache a) == desc_hash_dir c (cached_payload cache' a));
            ()
          )
        )
    
let eac_ptrfn_aux (l:eac_log) (n:bin_tree_node) (c:bin_tree_dir):
  option (d:bin_tree_node{is_desc d (child c n)}) = 
  if depth n >= addr_size then None
  else (
    let dh = desc_hash_dir c (eac_payload l n) in
    match dh with
    | Empty -> None
    | Desc d h -> 
      lemma_eac_payload_empty_or_points_to_desc l n c;
      Some d
  )
    
let eac_ptrfn (l:eac_log): ptrfn =
  eac_ptrfn_aux l

let ptrfn_unchanged (e:verifier_log_entry): bool = 
  match e with
  | MemoryOp _ -> true
  | Evict _ _ -> true
  | Add _ _ _ -> false

let lemma_update_desc_hash (a:merkle_addr) (v:merkle_payload_of_addr a)
                     (d:merkle_addr {is_proper_desc d a}) (h:hash_value)
  : Lemma (desc_hash_dir (other_dir (desc_dir d a)) v = 
           desc_hash_dir (other_dir (desc_dir d a)) (update_desc_hash a v d h)) = ()

let lemma_ptrfn_unchanged_memoryop (l:eac_log{length l > 0}) 
                                   (a:merkle_non_leaf_addr)
                                   (c:bin_tree_dir):
  Lemma (requires (MemoryOp? (telem l)))
        (ensures (eac_ptrfn l a c = eac_ptrfn (hprefix l) a c)) = 
  let n = length l in
  let cache = cache_at_end l in
  let l' = hprefix l in
  let cache' = cache_at_end l' in
  
  lemma_changes_caching l a;
  assert(cache_contains cache a = cache_contains cache' a);
  
  if cache_contains cache a then ()
  else (
    lemma_last_index_last_elem_nsat (is_evict_of_addr a) l;
    if has_some_evict l a then 
      lemma_last_index_prefix (is_evict_of_addr a) l (n - 1)          
    else ()
  )    

let lemma_ptrfn_unchanged_evictA (l:eac_log{length l > 0}) 
                                 (a:merkle_non_leaf_addr)
                                 (c:bin_tree_dir):
  Lemma (requires (Evict? (telem l) /\
                   Evict?.a (telem l) = a))
        (ensures (eac_ptrfn l a c = eac_ptrfn (hprefix l) a c)) = 
  let l' = hprefix l in
  let cache' = cache_at_end l' in        
  lemma_last_index_last_elem_sat (is_evict_of_addr a) l;
  assert(eac_payload l a = eac_payload l' a);  
  ()

let lemma_ptrfn_unchanged_evictB (l:eac_log{length l > 0}) 
                                 (a:merkle_non_leaf_addr)
                                 (c:bin_tree_dir):
  Lemma (requires (Evict? (telem l) /\
                   Evict?.a' (telem l) = a))
        (ensures (eac_ptrfn l a c = eac_ptrfn (hprefix l) a c)) = 
  let e = telem l in
  let a1 = Evict?.a e in
  let ce = desc_dir a1 a in
  if ce = c then ()
  else ()

let lemma_ptrfn_unchanged_evictC (l:eac_log{length l > 0}) 
                                 (a:merkle_non_leaf_addr)
                                 (c:bin_tree_dir):
  Lemma (requires (Evict? (telem l) /\
                   Evict?.a (telem l) <> a /\
                   Evict?.a' (telem l) <> a))
        (ensures (eac_ptrfn l a c = eac_ptrfn (hprefix l) a c)) = 
  let n = length l in
  let cache = cache_at_end l in
  let l' = hprefix l in
  let cache' = cache_at_end l' in
  assert(cache_contains cache a = cache_contains cache' a);
  if cache_contains cache a then ()
  else (
    lemma_last_index_last_elem_nsat (is_evict_of_addr a) l;
    if has_some_evict l a then 
      lemma_last_index_prefix (is_evict_of_addr a) l (n - 1)          
    else ()
  )

(* if the last element is not an add, then the pointer function is unchanged *)
let lemma_ptrfn_unchanged (l:eac_log{length l > 0}):
  Lemma (requires (ptrfn_unchanged (telem l)))
        (ensures (feq_ptrfn (eac_ptrfn l) (eac_ptrfn (hprefix l)))) =
  let aux (a:bin_tree_node) (c:bin_tree_dir):
    Lemma (requires (True))
          (ensures (eac_ptrfn l a c = eac_ptrfn (hprefix l) a c)) 
          [SMTPat (eac_ptrfn l a c)]
          =
    let n = length l in
    if depth a >= addr_size then ()
    else (
      assert(not (is_merkle_leaf a));
      let pf = eac_ptrfn l in
      let cache = cache_at_end l in
      let e = telem l in
      let l' = hprefix l in
      let cache' = cache_at_end l' in
      let pf' = eac_ptrfn l' in
      match e with
      | MemoryOp _ -> lemma_ptrfn_unchanged_memoryop l a c
      | Evict a1 a2 ->
        if a1 = a then
          lemma_ptrfn_unchanged_evictA l a c
        else if a2 = a then 
          lemma_ptrfn_unchanged_evictB l a c        
        else 
          lemma_ptrfn_unchanged_evictC l a c        
    ) in  
  ()

let lemma_ptrfn_addA (l:eac_log{length l > 0})
                     (a:merkle_non_leaf_addr)
                     (c:bin_tree_dir):
  Lemma (requires (Add? (telem l) /\
                   a <> Add?.a (telem l) /\
                   a <> Add?.a' (telem l)))
        (ensures (eac_ptrfn l a c = eac_ptrfn (hprefix l) a c)) = 
  let n = length l in
  let e = telem l in
  let l' = hprefix l in
  let cache = cache_at_end l in
  let cache' = cache_at_end l' in
  match e with
  | Add a1 _ a2 ->
    assert(cache_contains cache a = cache_contains cache' a);
    if cache_contains cache a then ()
    else (
      lemma_last_index_last_elem_nsat (is_evict_of_addr a) l;
      if has_some_evict l a then 
        lemma_last_index_prefix (is_evict_of_addr a) l (n - 1)
      else
        ()
    )

let lemma_ptrfn_addB (l:eac_log{length l > 0})
                     (a:merkle_non_leaf_addr)
                     (c:bin_tree_dir):
  Lemma (requires (Add? (telem l) /\
                   a = Add?.a' (telem l) /\
                   points_to (eac_ptrfn (hprefix l)) (Add?.a (telem l)) a))
        (ensures (eac_ptrfn l a c = eac_ptrfn (hprefix l) a c)) = 
  let e = telem l in
  let a1 = Add?.a e in
  let ca1a = desc_dir a1 a in
  if c = ca1a then ()
  else ()

let lemma_ptrfn_addC (l:eac_log{length l > 0})
                     (a:merkle_non_leaf_addr)
                     (c:bin_tree_dir):
  Lemma (requires (Add? (telem l) /\
                   a = Add?.a (telem l) /\
                   points_to (eac_ptrfn (hprefix l)) a (Add?.a' (telem l))))
        (ensures (eac_ptrfn l a c = eac_ptrfn (hprefix l) a c)) = 
  let e = telem l in
  let a' = Add?.a' e in
  let l' = hprefix l in
  assert(eac_payload l' a = eac_payload l a);
  ()

let lemma_ptrfn_unchanged_add (l:eac_log{length l > 0}):
  Lemma (requires (Add? (telem l) /\
                   points_to (eac_ptrfn (hprefix l)) (Add?.a (telem l)) (Add?.a' (telem l))))
        (ensures (feq_ptrfn (eac_ptrfn l) (eac_ptrfn (hprefix l)))) = 
  let e = telem l in
  let l' = hprefix l in
  let pf' = eac_ptrfn l' in
  match e with
  | Add a _ a' -> 
    assert(points_to pf' a a');
    let aux (a1:bin_tree_node) (c:bin_tree_dir):
      Lemma (requires (True))
            (ensures (eac_ptrfn l a1 c = eac_ptrfn l' a1 c))
            [SMTPat (eac_ptrfn l a1 c)] = 
      if depth a1 >= addr_size then ()
      else if a1 = a then 
        lemma_ptrfn_addC l a c      
      else if a' = a1 then
        lemma_ptrfn_addB l a1 c
      else 
        lemma_ptrfn_addA l a1 c      
    in
    ()

let lemma_points_to_after_add (l:eac_log{length l > 0}):
  Lemma (requires (Add? (telem l)))
        (ensures (points_to (eac_ptrfn l) (Add?.a (telem l)) (Add?.a' (telem l)))) = ()

let lemma_ptrfn_extend_add (l:eac_log{length l > 0}):
  Lemma (requires (Add? (telem l) /\
                   is_proper_desc (Add?.a (telem l)) (Add?.a' (telem l)) /\
                   points_to_none (eac_ptrfn (hprefix l)) (Add?.a (telem l)) /\
                   root_reachable (eac_ptrfn (hprefix l)) (Add?.a' (telem l)) /\
                   not (points_to_some (eac_ptrfn (hprefix l)) 
                                       (Add?.a' (telem l))
                                       (desc_dir (Add?.a (telem l)) (Add?.a' (telem l))))))
        (ensures (feq_ptrfn (eac_ptrfn l) (extend_ptrfn (eac_ptrfn (hprefix l))
                                                        (Add?.a (telem l))
                                                        (Add?.a' (telem l))))) = 
  let e = telem l in
  let l' = hprefix l in
  let pf = eac_ptrfn l in
  let pf' = eac_ptrfn l' in
  let a = Add?.a e in 
  let a' = Add?.a' e in
  let c = desc_dir a a' in
  let pf'e = extend_ptrfn pf' a a' in
  let aux (a1:bin_tree_node) (c1:bin_tree_dir):
        Lemma (requires (True))
              (ensures (pf a1 c1 = pf'e a1 c1))
              [SMTPat (pf a1 c1)] = 
        if depth a1 >= addr_size then ()
        else if a1 = a then () 
        else if a1 = a' then
          if c1 = c then ()
          else ()
        else 
          lemma_ptrfn_addA l a1 c1        
 in
 assert(feq_ptrfn pf pf'e);
 ()

let lemma_ptrfn_extendcut_add (l:eac_log{length l > 0}):
  Lemma (requires (Add? (telem l) /\
                   is_proper_desc (Add?.a (telem l)) (Add?.a' (telem l)) /\
                   points_to_none (eac_ptrfn (hprefix l)) (Add?.a (telem l)) /\
                   points_to_some (eac_ptrfn (hprefix l)) 
                                  (Add?.a' (telem l)) 
                                  (desc_dir (Add?.a (telem l)) (Add?.a' (telem l))) /\
                   is_proper_desc (pointed_node (eac_ptrfn (hprefix l)) 
                                                (Add?.a' (telem l))
                                                (desc_dir (Add?.a (telem l)) (Add?.a' (telem l))))
                                  (Add?.a (telem l)) /\
                   root_reachable (eac_ptrfn (hprefix l)) (Add?.a' (telem l))))
        (ensures (feq_ptrfn (eac_ptrfn l) (extendcut_ptrfn (eac_ptrfn (hprefix l))
                                                           (Add?.a (telem l))
                                                           (Add?.a' (telem l))))) = 
  let e = telem l in
  let l' = hprefix l in
  let a = Add?.a e in
  let a' = Add?.a' e in
  let pf = eac_ptrfn l in
  let pf' = eac_ptrfn l' in
  let pf'e = extendcut_ptrfn pf' a a' in
  let aux (a1:bin_tree_node) (c1:bin_tree_dir):
        Lemma (requires (True))
              (ensures (pf a1 c1 = pf'e a1 c1))
              [SMTPat (pf a1 c1)] = 
        if depth a1 >= addr_size then ()
        else if a1 = a then
          ()
        else if a1 = a' then
          ()
        else
          lemma_ptrfn_addA l a1 c1
  in
  ()

let rec lemma_root_reachable_prefix (l:eac_log) (i:nat{i <= length l}) (a:merkle_addr):
  Lemma (requires (root_reachable (eac_ptrfn (prefix l i)) a))
        (ensures (root_reachable (eac_ptrfn l) a)) 
        (decreases (length l)) = 
  let n = length l in
  if n = 0 then ()
  else if i = n then ()
  else (
    let l' = hprefix l in
    lemma_root_reachable_prefix l' i a;
    assert(root_reachable (eac_ptrfn l') a);
    let e = telem l in
    let pf' = eac_ptrfn l' in
    match e with
    | MemoryOp _ -> lemma_ptrfn_unchanged l
    | Evict _ _ -> lemma_ptrfn_unchanged l 
    | Add a1 _ a2 ->
      if points_to pf' a1 a2 then
        lemma_ptrfn_unchanged_add l
      else if points_to_some pf' a2 (desc_dir a1 a2) then
        admit()
      else (
        assert(Add? (telem l));
        assert(is_proper_desc (Add?.a (telem l)) (Add?.a' (telem l)));
        assert(points_to_none (eac_ptrfn (hprefix l)) (Add?.a (telem l)));
        //lemma_ptrfn_extend_add l;
        admit()
      )
  )

let rec lemma_has_add_equiv_root_reachable (l:eac_log) (a:merkle_non_root_addr):
  Lemma (requires (True))
        (ensures (has_some_add l a <==> root_reachable (eac_ptrfn l) a))
        (decreases (length l)) = 
  let n = length l in
  let cache = cache_at_end l in
  let pf = eac_ptrfn l in
  if n = 0 then (
    lemma_root_is_univ_ancestor a;
    assert(None? (pf a (desc_dir a Root)));
    lemma_non_reachable_desc_of_none pf a Root
  )
  else (
    let l' = prefix l (n - 1) in
    let cache' = cache_at_end l' in
    let pf' = eac_ptrfn l' in   
    lemma_has_add_equiv_root_reachable l' a;
    let e = index l (n - 1) in
    match e with
    | Add a1 v1 a2 -> 
      let lemma_a2_root_reachable (): Lemma (root_reachable pf' a2) = 
        if a2 = Root then
          lemma_reachable_reflexive pf' Root
        else (
          lemma_has_add_equiv_root_reachable l' a2;
          lemma_cache_contains_implies_last_add_before_evict l' a2
        )
      in 
      lemma_a2_root_reachable();
      let c = desc_dir a1 a2 in
      lemma_points_to_after_add l;
      lemma_points_to_reachable pf a1 a2;
      assert(reachable pf a1 a2);
      if points_to pf' a1 a2 then (
        lemma_ptrfn_unchanged_add l;
        if a1 = a then (
          lemma_last_index_last_elem_sat (is_add_of_addr a) l;
          if a2 = Root then ()
          else (
            lemma_cache_contains_implies_last_add_before_evict l' a2;
            lemma_has_add_equiv_root_reachable l' a2;
            lemma_reachable_transitive pf a a2 Root
          )
        )
        else 
          lemma_last_index_last_elem_nsat (is_add_of_addr a) l        
      )
      else if points_to_some pf' a2 c then (        
        lemma_ptrfn_extendcut_add l;
        let pf'e = extendcut_ptrfn pf' a1 a2 in
        assert(feq_ptrfn pf pf'e);
        if a1 = a then (
          lemma_last_index_last_elem_sat (is_add_of_addr a) l;
          lemma_extendcut_reachable pf' a1 a2 a2;
          lemma_reachable_transitive pf a a2 Root
        )
        else (
          lemma_last_index_last_elem_nsat (is_add_of_addr a) l;
          if root_reachable pf' a then 
            lemma_extendcut_reachable pf' a1 a2 a          
          else 
            lemma_extendcut_not_reachable pf' a1 a2 a          
        )
      )
      else (        
        lemma_ptrfn_extend_add l;
        admit()
      )

    | _  ->
      assert(ptrfn_unchanged e);
      lemma_ptrfn_unchanged l;
      assert(feq_ptrfn pf pf');
      lemma_last_index_last_elem_nsat (is_add_of_addr a) l;
      lemma_reachable_feq pf pf' a Root;
      if has_some_add l a then
        lemma_last_index_prefix (is_add_of_addr a) l (n - 1)
      else
        lemma_not_exists_prefix (is_add_of_addr a) l (n - 1)
  )


