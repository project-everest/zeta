module Veritas.MerkleVerifier

open FStar.Seq
open FStar.BitVector
open FStar.Classical
open Veritas.SeqAux
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

(* index in the verifier log *)
type vl_index (l:verifier_log) = seq_index l

(* is the i'th operation an evict *)
let is_evict (l:verifier_log) (i:vl_index l): Tot bool =
  Evict? (index l i)

(* evicted address for an evict operation *)
let evict_addr (l:verifier_log) (i:vl_index l{is_evict l i}): Tot merkle_addr = 
  Evict?.a (index l i)

(* is the ith operation an add *)
let is_add (l:verifier_log) (i:vl_index l) = 
  Add? (index l i)

(* added address for an add operation *)
let add_addr (l:verifier_log) (i:vl_index l{is_add l i}): Tot merkle_addr = 
  Add?.a (index l i)

(* added payload for an add operation *)
let add_payload (l:verifier_log) (i:vl_index l {is_add l i}): Tot merkle_payload =
  Add?.v (index l i)

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
  | Write a v -> cache_update cache (addr_to_merkle_leaf a) (MkLeaf v)
  
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
(* TODO: Understand subtleties of noeq *)
noeq type verifier_state = 
  | Failed: verifier_state 
  | Valid: vc:verifier_cache -> verifier_state

(* 
 * Given a cache and merkle non-root node, check 
 * (1) the parent node is in the cache
 * (2) hash stored at the parent corresponds to the node
 *)
let is_parent_hash_correct (cache:verifier_cache) 
                           (a:merkle_non_root_addr) 
                           (v:merkle_payload_of_addr a): Tot bool =
  match a with
  | LeftChild p -> if cache_contains cache p then
                     (* parent node payload *)
                     let pv = Some?.v (cache p) in
                     (* check hash of v corresponds to the hash in parent *)
                     hashfn v = MkInternal?.left pv
                   else false
  | RightChild p -> if cache_contains cache p then
                     (* parent node payload *)
                     let pv = Some?.v (cache p) in
                     (* check hash of v corresponds to the hash in parent *)
                     hashfn v = MkInternal?.right pv
                   else false

(*
 * Given a cache and a merkle on-root node,
 * update the hash stored at the parent with the hash of the node 
 *)
let update_parent_hash (cache:verifier_cache)
                       (a:merkle_non_root_addr{cache_contains cache a && 
                                               cache_contains cache (parent a)})
  : Tot verifier_cache =
  (* hash of the node *)
  let h = hashfn (Some?.v (cache a)) in
  match a with
  | LeftChild p -> let pv = Some?.v (cache p) in
                   cache_update cache p (MkInternal h (MkInternal?.right pv))
                  
  | RightChild p -> let pv = Some?.v (cache p) in
                    cache_update cache p (MkInternal (MkInternal?.left pv) h)
                        
(* Each step of the verifier *)
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
          | Read _ v -> if v = MkLeaf?.value payload then vs else Failed            
          (* For writes, update the cache to reflect the write *)
          | Write a v -> Valid (cache_apply cache o))
    | Add a v -> 
        (* Check cache contains merkle addr *)
        if cache_contains cache a then Failed 
        (* Root is never added *)
        else if is_merkle_root a then Failed 
        (* Check payload structure corresponds to address *)
        else if is_payload_of_addr a v then
          (* Check if hash node is that stored in parent *)
          if is_parent_hash_correct cache a v then
            (* Add the new node to the cache and return *)
            Valid (cache_add cache a v)
          (* hash check failed *)
          else Failed
        else 
          (* Invalid payload *)
          Failed
    | Evict a -> 
        (* Merkle root is never evicted *)
        if is_merkle_root a then Failed
        else if cache_contains cache a && cache_contains cache (parent a) then
          (* update the parent hash and evict *)
          Valid (cache_evict (update_parent_hash cache a) a)
        else
          Failed

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
    merklefn a init_memory

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
        (decreases (length l)) = 
  let n = length l in
  if n = 0 then ()
  else if i = n then lemma_fullprefix_equal l
  else ( 
    lemma_verifiable_implies_prefix_verifiable (prefix l (n - 1)) i;
    lemma_prefix_prefix l (n - 1) i
  )

(* prefix, redefined for verifiable logs *)
let vprefix (l:verifiable_log) (i:nat{i <= length l}): Tot verifiable_log = 
  lemma_verifiable_implies_prefix_verifiable l i;prefix l i

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
 * Lemma: if there is a memory operation at index i, then cache at that position
 * contains the address touched by the operation 
 *)
let lemma_memop_requires_cache (l:verifiable_log) (i:vl_index l):
  Lemma (requires (is_memory_op l i))
        (ensures  (cache_contains (cache_at_end (vprefix l i)) 
                                  (addr_to_merkle_leaf (address_of (memory_op_at l i))))) = 
  lemma_verifiable_implies_prefix_verifiable l (i + 1);
  lemma_verifiable_implies_prefix_verifiable l i;
  lemma_prefix_index l (i + 1) i;
  lemma_prefix_prefix l (i + 1) i

(*
 * Lemma: An evict operation requires the cache to contain the evicted address 
 *)
let lemma_evict_requires_cache (l:verifiable_log) (i:vl_index l):
  Lemma (requires (is_evict l i))
        (ensures  (cache_contains (cache_at_end (vprefix l i)) (evict_addr l i))) = 
  lemma_verifiable_implies_prefix_verifiable l (i + 1);
  lemma_verifiable_implies_prefix_verifiable l i;
  lemma_prefix_index l (i + 1) i;
  lemma_prefix_prefix l (i + 1) i

(* Lemma: add operation requires cache not to contain the added address *)
let lemma_add_requires_not_cached (l:verifiable_log) (i:vl_index l):
  Lemma (requires (is_add l i))
        (ensures (not (cache_contains (cache_at_end (vprefix l i)) (add_addr l i)))) = 
  lemma_verifiable_implies_prefix_verifiable l (i + 1);
  lemma_verifiable_implies_prefix_verifiable l i;
  lemma_prefix_index l (i + 1) i;
  lemma_prefix_prefix l (i + 1) i
        
(*
 * Lemma: merkle root is never added
 *)
let lemma_root_never_added (l:verifiable_log) (i:vl_index l):
  Lemma (requires (is_add l i))
        (ensures (not (is_merkle_root (add_addr l i)))) = 
  lemma_verifiable_implies_prefix_verifiable l (i + 1);
  lemma_verifiable_implies_prefix_verifiable l i;
  lemma_prefix_index l (i + 1) i;
  lemma_prefix_prefix l (i + 1) i

(* Lemma: merkle root never evicted *)
let lemma_root_never_evicted (l:verifiable_log) (i:vl_index l):
  Lemma (requires (is_evict l i))
        (ensures (not (is_merkle_root (evict_addr l i)))) = 
  lemma_verifiable_implies_prefix_verifiable l (i + 1);
  lemma_verifiable_implies_prefix_verifiable l i;
  lemma_prefix_index l (i + 1) i;
  lemma_prefix_prefix l (i + 1) i        

let lemma_add_requires_parent_in_cache (l:verifiable_log) (i:vl_index l):
  Lemma (requires (is_add l i))
        (ensures (~(is_merkle_root (add_addr l i)) /\ 
                  cache_contains (cache_at_end (vprefix l i)) (parent (add_addr l i)))) =
  lemma_verifiable_implies_prefix_verifiable l (i + 1);
  lemma_verifiable_implies_prefix_verifiable l i;
  lemma_prefix_index l (i + 1) i;
  lemma_prefix_prefix l (i + 1) i

let lemma_evict_requires_parent_in_cache (l:verifiable_log) (i:vl_index l):
  Lemma (requires (is_evict l i))
        (ensures (~(is_merkle_root (evict_addr l i)) /\
                  cache_contains (cache_at_end (vprefix l i)) (parent (evict_addr l i)))) = 
  lemma_verifiable_implies_prefix_verifiable l (i + 1);
  lemma_verifiable_implies_prefix_verifiable l i;
  lemma_prefix_index l (i + 1) i;
  lemma_prefix_prefix l (i + 1) i                  

(* Does this log entry update the cache for address a *)
let updates_cache (a:merkle_addr) (e:verifier_log_entry): Tot bool = 
  match e with
  | MemoryOp o -> Write? o && addr_to_merkle_leaf (address_of o) = a
  | Add a' v -> a = a' 
  | Evict a' -> a = a' || not (is_merkle_root a') && 
                         parent a' = a 

(* 
 * The state of the cache is unchanged on a verifier step if the log entry does not 
 * update the cache 
 *)
let lemma_updates_cache (vc:verifier_cache) (a:merkle_addr) (e:verifier_log_entry):
  Lemma (requires (Valid? (verifier_step e (Valid vc)) && 
                   not (updates_cache a e) && cache_contains vc a))
        (ensures (cache_contains (Valid?.vc (verifier_step e (Valid vc))) a && 
                  Some?.v (vc a) = Some?.v (Valid?.vc (verifier_step e (Valid vc)) a))) = 
  let vc' = Valid?.vc (verifier_step e (Valid vc)) in
  match e with
  | MemoryOp o -> ()
  | Add a' v -> assert (a' <> a); 
                assert(vc' == cache_add vc a' v); 
                ()
  | Evict a' -> assert (a' <> a);
                assert (not (is_merkle_root a'));
                assert (parent a' <> a);
                let vc'' = update_parent_hash vc a' in
                assert (cache_contains vc'' a);
                assert (Some?.v (vc'' a) = Some?.v (vc a));
                assert (vc' == cache_evict vc'' a');
                ()

(* 
 * The state of the cache is unchanged on a verifier step if the log entry does not 
 * update the cache 
 *)
let lemma_updates_cache_inv (vc:verifier_cache) (a:merkle_addr) (e:verifier_log_entry):
  Lemma (requires (Valid? (verifier_step e (Valid vc)) && not (updates_cache a e) && 
                   cache_contains (Valid?.vc (verifier_step e (Valid vc))) a))
        (ensures (cache_contains vc a && 
                  Some?.v (vc a) = Some?.v (Valid?.vc (verifier_step e (Valid vc)) a))) = 
  let vc' = Valid?.vc (verifier_step e (Valid vc)) in
  match e with
  | MemoryOp e -> ()
  | Add a' v -> assert (a' <> a);
                assert (vc' == cache_add vc a' v);
                ()
  | Evict a' -> assert (a' <> a);
                assert (not (is_merkle_root a'));
                assert (parent a' <> a);
                let vc'' = update_parent_hash vc a' in
                assert (cache_contains vc'' a);
                assert (Some?.v (vc'' a) = Some?.v (vc a));
                assert (vc' == cache_evict vc'' a');
                ()

(* 
 * If the cache contains an address a (non root), then the last add/evict operation 
 * is an add 
 *)
let rec lemma_cache_contains_implies_last_add_before_evict (l:verifiable_log) (a:merkle_non_root_addr):
  Lemma (requires (cache_contains (cache_at_end l) a))
        (ensures (has_some_add l a /\
                  (has_some_evict l a ==> last_evict_idx l a < last_add_idx l a)))
        (decreases (length l)) = 
  let n = length l in
  let cache = cache_at_end l in
  let f_a = is_add_of_addr a in
  let f_e = is_evict_of_addr a in
  if n = 0 then ()
  else (
    let l' = vprefix l (n - 1) in
    let cache' = cache_at_end l' in
    let e = index l (n - 1) in

    (* e does not update the cache for address a *)
    if not (updates_cache a e) then (

      (* this implies that cache' also contains an entry for address a *)
      lemma_updates_cache_inv cache' a e;
      assert (cache_contains cache' a);

      (* applying induction on l' *)
      lemma_cache_contains_implies_last_add_before_evict l' a;

      (* l' has an add which implies l has an add *)
      let last_add_l' = last_add_idx l' a in
      lemma_prefix_index l (n - 1) last_add_l';
      lemma_last_index_correct2 f_a l last_add_l';
      assert (has_some_add l a);

      (* since e is not an (add a), last_add of l should be last_add of l' *)
      let last_add_l = last_add_idx l a in
      lemma_last_index_prefix f_a l (n - 1);
      assert (last_add_l = last_add_l');

      if (has_some_evict l a) then (
        let last_evict_l = last_evict_idx l a in
        (* since e is not an (evict a), last evict of l should be last_evict of l' *)
        lemma_last_index_prefix f_e l (n - 1);

        (* since the last add and last evict of l is same as that of l', the proof follows *)               
        ()
      )
      else (
        (* since l does not have an evict, l' does not have one too *)
        lemma_not_exists_prefix f_e l (n - 1);
        
        ()
      )
    )
    else (
      match e with
      | Add a' v -> assert (a' = a); // otherwise, it does not update cache for a

                    (* clearly this is the last add index for a *)
                    lemma_last_index_correct2 f_a l (n - 1);
                    assert(last_add_idx l a = (n - 1));

                    (* which implies last add is more recent than last evict as required *)
                    if has_some_evict l a then (
                      if last_evict_idx l a = n - 1 then ()
                      else ()
                    )
                    else ()

      | Evict a' -> if a = a' then () // if a is evicted, then it cannot be in the cache
                    else (      
                      (* the only reason evict a' updates the cache for a is if a = parent a' *)
                      assert (a = parent a'); 
                      (* but this implies that cache' contains a *)
                      assert (cache_contains cache' a);

                      (* applying induction *)
                      lemma_cache_contains_implies_last_add_before_evict l' a;

                      (* l' has an add which implies l has an add *)
                      let last_add_l' = last_add_idx l' a in
                      lemma_prefix_index l (n - 1) last_add_l';
                      lemma_last_index_correct2 f_a l last_add_l';
                      assert (has_some_add l a);

                      (* since e is not an (add a), last_add of l should be last_add of l' *)
                      let last_add_l = last_add_idx l a in
                      lemma_last_index_prefix f_a l (n - 1);
                      assert (last_add_l = last_add_l');

                      if (has_some_evict l a) then (
                        let last_evict_l = last_evict_idx l a in
                        (* since e is not an (evict a), last evict of l should be last_evict of l' *)
                        lemma_last_index_prefix f_e l (n - 1);

                        (* since the last add and last evict of l is same as that of l', the proof follows *)               
                        ()
                      )
                      else (
                        (* since l does not have an evict, l' does not have one too *)
                        lemma_not_exists_prefix f_e l (n - 1);
              
                        ()
                      )
                    )
      | MemoryOp o -> lemma_memop_requires_cache l (n - 1);
                      assert (cache_contains cache' a);
                      (* applying induction *)
                      lemma_cache_contains_implies_last_add_before_evict l' a;

                      (* l' has an add which implies l has an add *)
                      let last_add_l' = last_add_idx l' a in
                      lemma_prefix_index l (n - 1) last_add_l';
                      lemma_last_index_correct2 f_a l last_add_l';
                      assert (has_some_add l a);

                      (* since e is not an (add a), last_add of l should be last_add of l' *)
                      let last_add_l = last_add_idx l a in
                      lemma_last_index_prefix f_a l (n - 1);
                      assert (last_add_l = last_add_l');

                      if (has_some_evict l a) then (
                        let last_evict_l = last_evict_idx l a in
                        (* since e is not an (evict a), last evict of l should be last_evict of l' *)
                        lemma_last_index_prefix f_e l (n - 1);

                        (* since the last add and last evict of l is same as that of l', the proof follows *)               
                        ()
                      )
                      else (
                        (* since l does not have an evict, l' does not have one too *)
                        lemma_not_exists_prefix f_e l (n - 1);
              
                        ()
                      )
    )
  )


let rec lemma_not_contains_implies_last_evict_before_add (l:verifiable_log) (a:merkle_non_root_addr):
  Lemma (requires (not (cache_contains (cache_at_end l) a) && has_some_add l a))
        (ensures (has_some_evict l a && last_evict_idx l a > last_add_idx l a))
        (decreases (length l)) = 
  let n = length l in
  let cache = cache_at_end l in
  let f_a = is_add_of_addr a in
  let f_e = is_evict_of_addr a in
  let last_add_l = last_add_idx l a in

  if n = 0 then ()
  else (
    let l' = vprefix l (n - 1) in
    let cache' = cache_at_end l' in
    let e = index l (n - 1) in

    (* e does not update the cache for address a *)
    if not (updates_cache a e) then (

      (* if cache' contains a, then cache should also contain a, a contradiction *)
      if cache_contains cache' a then 
        lemma_updates_cache cache' a e
              
      else (
        assert (not (cache_contains cache' a));

        (* to apply induction we want to show that l' has some add to a *)

        (* last add in l cannot be n - 1 since, that would imply e is an add *)
        if last_add_l = n - 1 then ()

        else (
          (* there last_add_l < n - 1 which means there is an add in l' *)
          lemma_last_index_prefix f_a l (n - 1);
          assert (has_some_add l' a);

          (* apply induction on l' *)
          lemma_not_contains_implies_last_evict_before_add l' a;

          (* induction implies l' has an evict after last add *)
          let last_evict_l' = last_evict_idx l' a in

          (* since e is neither add or evict, last_evict and last_add 
           * of l' and l are identical from which the post-condition follows *)
          lemma_prefix_index l (n - 1) last_evict_l';
          lemma_last_index_correct2 f_e l last_evict_l';
          assert (has_some_evict l a);

          let last_evict_l = last_evict_idx l a in
          assert (last_evict_l < n - 1);
          lemma_last_index_prefix f_e l (n - 1);
          ()
        )
      )
    )
    else (
      match e with
      | Add a' v -> assert (a = a'); // otherwise handled in not-updates-cache
                    (* nothing to prove since Add a implies a is in cache *)
                    () 

      | Evict a' -> if a = a' then (
                      (* since e is Evict a, last evict in l is n - 1 *)
                      lemma_last_index_correct2 f_e l (n - 1);
                      let last_evict_l = last_evict_idx l a in
                      assert (last_evict_l = n - 1);

                      if last_add_l = n - 1 then ()
                      else ()                      
                    )
                    else (
                      (* the only reason evict a' updates the cache for a is if a = parent a' *)
                      assert (a = parent a'); 
                      (* but this implies that cache' contains a *)
                      assert (cache_contains cache' a);

                      (* which implies cache contains a, a contradiction *)
                      lemma_updates_cache cache' a e
                    )
      | MemoryOp o -> lemma_memop_requires_cache l (n - 1);
                      assert (cache_contains cache' a);
                      (* which implies cache contains a, a contradiction *)
                      lemma_updates_cache cache' a e
    )
  )


(* Lemma: there is an evict operation between every two add operations of an address *)
let lemma_evict_between_adds (l:verifiable_log) 
                             (i1:vl_index l{is_add l i1}) 
                              (i2:vl_index l{is_add l i2 && add_addr l i1 = add_addr l i2 && i2 > i1}):
  Lemma (requires (True))
        (ensures (has_some_evict (prefix l i2) (add_addr l i2) && 
                  last_evict_idx (prefix l i2) (add_addr l i2) > i1))
        (decreases (length l)) = 
  let a = add_addr l i2 in
  let f_a = is_add_of_addr a in
  let f_e = is_evict_of_addr a in  
  (* log before i2 add is processed *)
  let l2 = vprefix l i2 in
  (* cache before i2 add is processed *)
  let cache2 = cache_at_end l2 in
  (* since the i2 add succeeded, cache1 should not contain a *)
  lemma_add_requires_not_cached l i2;
  assert (not (cache_contains cache2 a));

  (* this implies the last add/evict operation before i1 to a was an evict *)
  lemma_prefix_index l i2 i1;
  lemma_last_index_correct2 f_a l i1;
  lemma_root_never_added l i2;
  lemma_last_index_correct2 f_a l2 i1;
  lemma_not_contains_implies_last_evict_before_add l2 a

(* Lemma: there is an add operation between every two evict operations of an address *)
let rec lemma_add_between_evicts (l:verifiable_log)
                                 (i1:vl_index l{is_evict l i1})
                                 (i2:vl_index l{is_evict l i2 && evict_addr l i1 = evict_addr l i2 && i2 > i1}):
  Lemma (requires (True))
        (ensures (has_some_add (prefix l i2) (evict_addr l i2) &&
                  last_add_idx (prefix l i2) (evict_addr l i2) > i1))
        (decreases (length l)) = 
  let a = evict_addr l i2 in
  let f_a = is_add_of_addr a in
  let f_e = is_evict_of_addr a in
  (* log before i2 evict is processed *)
  let l2 = vprefix l i2 in
  (* cache before i2 evict is processed *)
  let cache2 = cache_at_end l2 in
  (* since i2 evict succeeded cache should contain a *)
  lemma_evict_requires_cache l i2;
  assert (cache_contains cache2 a);

  (* this implies the last add/evict operation before i2 was an add *)
  lemma_prefix_index l i2 i1;
  lemma_last_index_correct2 f_e l i1;
  lemma_root_never_evicted l i2;
  lemma_last_index_correct2 f_e l2 i1;
  lemma_cache_contains_implies_last_add_before_evict l2 a 

(* Lemma: There is an add before the first evict *)
let lemma_first_add_before_evict (l:verifiable_log) 
                                     (i:vl_index l{is_evict l i})
  : Lemma (requires (True))
          (ensures (has_some_add (prefix l i) (evict_addr l i)))
          (decreases (length l)) = 
  let a = evict_addr l i in
  let f_a = is_add_of_addr a in
  let f_e = is_evict_of_addr a in  
  (* log before evict at i is processed *)
  let l' = vprefix l i in
  (* cache before evict at i is processed *)
  let cache' = cache_at_end l' in
  (* since the evict at i succeeded, cache' should contain a *)
  lemma_evict_requires_cache l i;
  assert (cache_contains cache' a);

  (* a is not merkle_root since it is evicted *)
  lemma_root_never_evicted l i;

  (* since cache contains a, it implies a previous add *)
  lemma_cache_contains_implies_last_add_before_evict l' a;
  ()
    

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
  lemma_verifiable_implies_prefix_verifiable l (i + 1);
  lemma_verifiable_implies_prefix_verifiable l i;
  let a = evict_addr l i in
  let l'' = prefix l i in
  let vs'' = verifier l'' in 
  lemma_prefix_prefix l (i + 1) i;
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
    add_payload l i = last_evict_value_or_init (vprefix l i) (add_addr l i)

(* evict-add consistency is a computable property *)
let is_evict_add_consistent (l:verifiable_log): 
  Tot (b:bool{b <==> evict_add_consistent l}) = admit()

(* refinement of verifiable logs that are evict-add consistent *)
type eac_log  = l:verifiable_log {evict_add_consistent l}

(* Part I of the proof: we prove that evict-add consistency implies rw-consistency *)

(* 
 * for a merkle leaf address - which corresponds to a memory address  - 
 * the last written value or Null 
 *)
let last_write_value_or_null (l:verifiable_log) (a:merkle_leaf_addr)
  : Tot (merkle_payload_of_addr a) =
  if has_some_write l a then
    MkLeaf (written_value l (last_write_idx l a))
  else
    MkLeaf Null

(* 
 * If the last entry of the log does not write to a, then last_write_value remains unchanged 
 *)
let lemma_last_write_unchanged_unless_write (l:verifiable_log{length l > 0}) (a:merkle_leaf_addr):
  Lemma (requires (not (is_write_to_addr a (index l (length l - 1)))))
        (ensures (last_write_value_or_null l a = 
                  last_write_value_or_null (prefix l (length l - 1)) a)) =
  admit() 

(* Lemma: prefix of evict-add-consistent log is evict-add-consistent *)
let lemma_eac_prefix (l:eac_log) (i:nat{i <= length l}):
  Lemma (requires (True))
        (ensures (evict_add_consistent (vprefix l i))) =
  let l' = vprefix l i in 
  let aux (j:vl_index l'):
    Lemma (is_add (prefix l i) j ==>
           add_payload (prefix l i) j = last_evict_value_or_init (vprefix (vprefix l i) j) 
                                                                   (add_addr (prefix l i) j)) = 
    let l' = vprefix l i in
    if not (is_add l' j) then ()
    else (
      lemma_prefix_index l i j;
      assert (is_add l' j);
      lemma_prefix_prefix l i j;
      assert(vprefix l j = vprefix l' j)
    )
    in
    forall_intro aux
    
(* 
 * The core lemma of part I, the cached value of every leaf node reflects the 
 * last write or Null if the log is evict-add consistent 
 *)
let rec lemma_eac_implies_cache_is_last_write (l:eac_log) (a:merkle_leaf_addr):
  Lemma (requires (True))
        (ensures (cache_contains (cache_at_end l) a ==> 
                  Some?.v ((cache_at_end l) a) = last_write_value_or_null l a))
        (decreases (length l)) = 
  let n = length l in
  (* current cache *)
  let cache = cache_at_end l in
  if n = 0 then ()
  (* nothing to prove if cache does not contain a *)
  else if (not (cache_contains cache a)) then ()
  else (
    assert(cache_contains cache a);
    
    lemma_cache_contains_implies_last_add_before_evict l a;

    (* Induction step on l' *)
    let l' = vprefix l (n - 1) in
    lemma_eac_prefix l (n - 1);
    lemma_eac_implies_cache_is_last_write l' a;

    (* current log entry *)
    let e = index l (n - 1) in 

    (* cache after l' *)
    let cache' = (cache_at_end l') in

    (* cache is obtained after processing e on cache' *)
    assert (Valid cache == verifier_step e (Valid cache'));

    if (not (updates_cache a e)) then (
      (* since e does not update the cache for address a ... *)
      lemma_updates_cache_inv cache' a e;

      (* cache' should contain address a since cache contains it *)
      assert(cache_contains cache' a);
      assert(Some?.v (cache' a) = Some?.v (cache a));   // I

      (* from induction we know that *)
      assert(Some?.v (cache' a) = last_write_value_or_null l' a); // II 
      
      (* Entry e is not a write to a, so last_write_value is unchanged *)
      lemma_last_write_unchanged_unless_write l a;
      assert (last_write_value_or_null l' a = last_write_value_or_null l a); // III

      () // follows from I,II,III
    )
    else (
      assert (updates_cache a e); // we disposed off the case of not updates cache

      match e with
      | Evict a' -> 
        (* If I have evicted a then cache does not contain a =><= *)
        if a' = a then ()

        (* Evict a' <> a does not update cache, which is a contradiction *)
        else () 
      | Add a' v -> 
        if a' = a then (
          (* since l is evict - add consistent, this add payload reflects previous evict or null *)
          assert (is_add l (n - 1));
          assert (v = last_evict_value_or_init l' a);

          (* add semantics *)
          assert(Some?.v (cache a) = v);

          (* Case A: there was a previous Evict a *)
          if has_some_evict l a then (
            let f_e = is_evict_of_addr a in
            let f_w = is_write_to_addr a in
            let lei = last_evict_idx l a in
            lemma_last_index_prefix f_e l (n - 1);
            lemma_prefix_prefix l (n - 1) lei;
            lemma_prefix_index l (n - 1) lei;

            (* it follows that v is payload evicted at lei *)
            assert (v = evict_payload l lei);

            let l_lei_pre = vprefix l lei in
            
            (* Apply induction at lei *)
            lemma_eac_prefix l lei;
            lemma_eac_implies_cache_is_last_write l_lei_pre a;                

            (* cache at lei *)
            let cache_lei_pre = (cache_at_end l_lei_pre) in

            (* since lei is an evict, cache_lei_pre should contain a *)
            lemma_evict_requires_cache l lei;
            assert(cache_contains cache_lei_pre a);

            (* evict payload at lei is the cache_lei_pre a *)
            assert (v = Some?.v (cache_lei_pre a));

            (* from induction ... *)
            assert(Some?.v (cache_lei_pre a) = last_write_value_or_null l_lei_pre a);

            (* Case A1 - there is some write to a *)
            if has_some_write l a then (
              (* lwi = index of the last write *)
              let lwi = last_write_idx l a in

              (* we want to show that lwi occurs before lei, before the last evict *)
              assert (lwi <> lei);
              if (lwi > lei) then (
                (* If we assume lwi occurs after lei *)
                lemma_memop_requires_cache l lwi;
                let l_lwi_pre = vprefix l lwi in
                lemma_cache_contains_implies_last_add_before_evict l_lwi_pre a;
                (* last add before lwi *)
                let lai_pre_lwi = last_add_idx l_lwi_pre a in

                (* since lei is before lwi, there exists an evict before lwi *)
                lemma_prefix_index l lwi lei;
                lemma_last_index_correct2 f_e l_lwi_pre lei; 
                let lei' = last_evict_idx l_lwi_pre a in                
                assert(lei' >= lei);
                assert(lai_pre_lwi > lei');

                lemma_prefix_index l lwi lai_pre_lwi;
                assert(is_add l lai_pre_lwi);

                (* 
                 * the last add before lwi happens after lei. the two adds
                 * n-1 and lai_pre_lwi imply another evict between which
                 * is a contradiction 
                 *)
                lemma_evict_between_adds l lai_pre_lwi (n - 1)                
              )
              else (
                assert(lwi < lei);
                lemma_prefix_index l lei lwi;
                lemma_last_index_prefix f_w l lei;
                assert(last_write_idx l_lei_pre a = lwi);
                assert(last_write_value_or_null l a = last_write_value_or_null l_lei_pre a);
                ()
              )
            )
            else 
              (* There is no write to a => last_write_value is Null as required *)
              lemma_not_exists_prefix f_w l lei            
          )
          (* Case B: there was no previous Evict a *)
          else (
            (* l does not have evict => l' does not have an evict *)
            let f = is_evict_of_addr a in
            lemma_not_exists_prefix f l (n - 1);
            assert (not (has_some_evict l' a));

            (* this implies .... *)
            assert (last_evict_value_or_init l' a = MkLeaf Null);
            assert (v = MkLeaf Null);

            (* Now, we prove that there are no previous writes, so last_write_value_or_null is also Null *)
            if has_some_write l a then (
              (* If there is a previous write, lwi is the index of the last write *)
              let lwi = last_write_idx l a in
              lemma_memop_requires_cache l lwi;

              (* after processing upto lwi, cache should contain address a *)
              assert (cache_contains (cache_at_end (prefix l lwi)) a);

              (* if cache contains address a at lwi, then there should be a prior add a *)
              lemma_cache_contains_implies_last_add_before_evict (vprefix l lwi) a;
              assert (has_some_add (vprefix l lwi) a);

              (* if lai is the index of the last add before lwi *)
              let lai = last_add_idx (vprefix l lwi) a in
              lemma_prefix_index l lwi lai;
              assert (is_add l lai);

              (* this implies an evict between lai and (n - 1), a contradiction *)
              lemma_evict_between_adds l lai (n - 1)
            )
            else ()                          
          )
        )
        else ()
      | MemoryOp o -> 
        if Read? o then () // handled in does not update cache
        else if a = addr_to_merkle_leaf (Write?.a o) then (
          lemma_merkle_equal_implies_addr_equal (merkle_leaf_to_addr a) (Write?.a o);
          let f_w = is_write_to_addr a in
          lemma_last_index_correct2 f_w l (n - 1)          
        )
        else 
          ()          

    )
  )

(* evict-add consistency implies every read corresponds to the last write *)
let lemma_eac_implies_read_last_write (l:eac_log) (i:vl_index l):
  Lemma (requires (is_read_op l i))
        (ensures (MkLeaf (read_value l i) = 
                  last_write_value_or_null (vprefix l i) 
                                           (addr_to_merkle_leaf (Read?.a (memory_op_at l i))))) = 
  let l' = vprefix l i in
  let a = addr_to_merkle_leaf (address_of (memory_op_at l i)) in

  (* the cache at i contains address of read *)
  lemma_memop_requires_cache l i;
  let cache = cache_at_end l' in
  assert (cache_contains cache a);

  (* l' is evict-add consistent *)  
  lemma_eac_prefix l i;

  (* cache at i stores last write *)
  lemma_eac_implies_cache_is_last_write l' a;

  (* read value is the cache value; the lemma follows *)
  assert(Some?.v (cache a) = last_write_value_or_null l' a);
  let l'' = vprefix l (i + 1) in
  lemma_prefix_prefix l (i + 1) i;
  lemma_prefix_index l (i + 1) i

(* is this verifier log entry a memory operation *)
let is_entry_memory_op (e:verifier_log_entry): Tot bool = 
  MemoryOp? e

(* the memory operation of an entry *)
let memory_op_of_entry (e:verifier_log_entry{is_entry_memory_op e}): Tot memory_op = 
    MemoryOp?.o e

(* project out the memory operations of a verifier log *)
let memory_ops_of (l:verifier_log): Tot memory_op_log = 
  map memory_op_of_entry (filter is_entry_memory_op l)

(* 
 * Final lemma of part I: evict-add consistency implies rw-consistency of the 
 * projected memory operations *)
let lemma_eac_implies_rw_consistency (l:eac_log):
  Lemma (requires (True))
        (ensures (rw_consistent (memory_ops_of l))) =
  let lm = memory_ops_of l in 
  let f = is_entry_memory_op in
  let fl = filter f l in
  let aux (i:log_index lm):
    Lemma (Memory.is_read_op lm i ==> 
           Memory.read_value lm i = 
           Memory.last_write_value_or_null (prefix lm i) (address_at_idx lm i)) =
    if Memory.is_read_op lm i then (
      (* i' is the index of operation read op i in verifier log *)
      let i' = filter_index_inv_map f l i in
      lemma_map_index memory_op_of_entry fl i;
      assert(filter_index_map f l i' = i);
      assert(is_read_op l i');
      assert(Memory.read_value lm i = read_value l i');

      (* Using lemma, the read value at l[i'] is the last write value *)
      let a = address_of (memory_op_at l i') in
      let ma = addr_to_merkle_leaf a in      
      lemma_addr_merkle_inv a;
      let f_w' = is_write_to_addr ma in
      let f_w = Memory.is_write_to_addr a in
      let l_pre_i' = vprefix l i' in
      let lm_pre_i = prefix lm i in
      lemma_eac_implies_read_last_write l i';
      assert(MkLeaf (read_value l i') = last_write_value_or_null l_pre_i' ma);

      if has_some_write l_pre_i' ma then (
        (* Case A: there is a write before i' *)
        (* let lw' be the index of this write *)
        let lw' = last_write_idx l_pre_i' ma in
        lemma_prefix_index l i' lw';

        (* lw is its mapping in lm *)
        let lw = filter_index_map f l lw' in
        lemma_filter_maps_correct f l lw';       
        lemma_map_index memory_op_of_entry fl lw;
        filter_index_map_monotonic is_entry_memory_op l lw' i';        

        (* We want to prove that lw is the last write before i which completes
         * the proof that read at i reads last write value *)
        lemma_prefix_index lm i lw;
        lemma_last_index_correct2 f_w lm_pre_i lw;

        (* let lw_2 be the last write *)
        let lw_2 = Memory.last_write_idx lm_pre_i a in
        assert (lw_2 >= lw);
        lemma_prefix_index lm i lw_2;

        if (lw_2 = lw) then ()

        else (
          let lw'_2 = filter_index_inv_map f l lw_2 in
          filter_index_inv_map_monotonic f l lw_2 i;
          filter_index_inv_map_monotonic f l lw lw_2;
          lemma_map_index memory_op_of_entry fl lw_2;          
          lemma_prefix_index l i' lw'_2;
          lemma_last_index_correct2 f_w' l_pre_i' lw'_2
        )
      )
      else (      
        (* Case B: there is no write to a before j' *)
        (* this implies last write is "null" *)
        assert(last_write_value_or_null l_pre_i' ma = MkLeaf Null);

        (* we want to prove there is no prior write in memory log before i *)
        if Memory.has_some_write lm_pre_i a then (
          (* if there is a write, lw_pre_i is index of last write before i *)
          let lw_pre_i = Memory.last_write_idx lm_pre_i a in
          assert(lw_pre_i < i);

          (* lw_pre_i' is its corresponding index in l *)
          let lw_pre_i' = filter_index_inv_map f l lw_pre_i in
          lemma_prefix_index lm i lw_pre_i;
          lemma_map_index memory_op_of_entry fl lw_pre_i;

          (* lw_pre_i' < i' *)
          filter_index_inv_map_monotonic is_entry_memory_op l lw_pre_i i;
          assert (lw_pre_i' < i');

          lemma_prefix_index l i' lw_pre_i';
          assert(is_write_to_addr ma (index l_pre_i' lw_pre_i'));

          lemma_last_index_correct2 f_w' l_pre_i' lw_pre_i'          
        )
        else ()
      )
    )
    else ()
  in
  forall_intro aux;
  lemma_rw_consistent_operational_correct lm

(* Part II of the proof: lack of evict-add consistency implies hash collision *)

let lemma_last_evict_or_init_of_child_unchanged (l:verifiable_log) (a:merkle_non_root_addr):
  Lemma (requires (has_some_evict l (parent a) && 
                   has_some_add l (parent a) && 
                   last_add_idx l (parent a) < last_evict_idx l (parent a)))
        (ensures (last_evict_value_or_init l a = 
                  last_evict_value_or_init (vprefix l (last_evict_idx l (parent a))) a)) = 
  let p = parent a in
  (* last evict of parent *)
  let ple = last_evict_idx l p in
  (* last add of parent *)
  let pla = last_add_idx l p in

  (* log just before p was evicted *)
  let l_ple = vprefix l ple in 

  (* p cannot be the root since it is added/evicted *)
  lemma_root_never_added l pla;
  assert(not (is_merkle_root p));

  if has_some_evict l a then
    (* index of last evict of address a *)
    let ale = last_evict_idx l a in
    assert (ale <> ple);
    assert (ale <> pla);

    if ale > ple then
      (* we prove that last evict of a cannot be after last evict of parent p *)
      let l_ale = vprefix l ale in
      let cache_ale = cache_at_end l_ale in

      (* when a is evicted, parent p should be in the cache *)
      lemma_evict_requires_parent_in_cache l ale;
      assert(cache_contains cache_ale p);

      lemma_last_index_prefix (is_evict_of_addr p) l ale;
      lemma_last_index_prefix (is_add_of_addr p) l ale;
      assert (last_add_idx l_ale p = pla);
      assert (last_evict_idx l_ale p = ple);

      (* since cache contains p, the last evict of p should be before last add of p *)
      (* in other words, pla < ple, which is a contradition *)
      lemma_cache_contains_implies_last_add_before_evict l_ale p
    else 
      (* last evict of a before last evict of p *)
      lemma_last_index_prefix (is_evict_of_addr a) l ple;
      (* which implies last_evict_value is the same for l and l_ple as required *)
      lemma_prefix_prefix l ple ale
  else
    (* address a is not evicted in l => address a not evicted in l_ple *)
    (* the post-condition follows since both last_evict_value_or_init is init for both l & l_ple *)    
    lemma_not_exists_prefix (is_evict_of_addr a) l ple


(* 
 * evict-add consistency implies that whenever an internal merkle addr is in
 * cache, its payload reflects the last evicts of its child nodes 
 *)
let rec lemma_eac_implies_cache_is_last_evict 
    (l:eac_log) 
    (a:merkle_non_leaf_addr{cache_contains (cache_at_end l) a && 
                            Some?.v ((cache_at_end l) a) <> 
                              MkInternal (hashfn (last_evict_value_or_init l (LeftChild a)))
                                         (hashfn (last_evict_value_or_init l (RightChild a)))})
  : Tot hash_collision (decreases (length l)) = 
  let n = length l in
  let cache = cache_at_end l in
  if n = 0 then 
    if is_merkle_root a then (
      assert (cache_contains cache a);
      assert (Some?.v (cache a) = MkInternal (hashfn (last_evict_value_or_init l (LeftChild a)))
                                             (hashfn (last_evict_value_or_init l (RightChild a))));
      Collision (MkLeaf Null) (MkLeaf Null)
    )
    else (
      assert (not (cache_contains cache a));
      Collision (MkLeaf Null) (MkLeaf Null)
    )
  
  else 
    let l' = vprefix l (n - 1) in
    (* l' is evict add consistent *)
    lemma_eac_prefix l (n - 1);
    let cache' = cache_at_end l' in
    let e = index l (n - 1) in

    if not (updates_cache a e) then (
      (* if e does not update cache for address a then cache' and cache agree on a *)
      lemma_updates_cache_inv cache' a e;

      assert(Some?.v (cache' a) <> MkInternal (hashfn (last_evict_value_or_init l (LeftChild a)))
                                             (hashfn (last_evict_value_or_init l (RightChild a))));
      
      let lemma_last_evict_unchanged (a': merkle_non_root_addr {parent a' = a}):
        Lemma (last_evict_value_or_init l a' = last_evict_value_or_init l' a') = 
        let f_e = is_evict_of_addr a' in
        if has_some_evict l a' then (
          let last_evict_l = last_evict_idx l a' in
          
          if last_evict_l = n - 1 then 
            // this implies e is evict a', which is a contradiction since e would 
            // then update cache for address a
            () 
          else 
            lemma_last_index_prefix f_e l (n - 1);
            lemma_prefix_prefix l (n - 1) last_evict_l;
            ()          
        ) 
        else 
          lemma_not_exists_prefix f_e l (n - 1)
      in

      lemma_last_evict_unchanged (LeftChild a);
      lemma_last_evict_unchanged (RightChild a);
      
      (* recursion gives the hash collision *)
      lemma_eac_implies_cache_is_last_evict l' a
    )
    else 
      match e with
      | Add a' v -> assert(a = a'); // otherwise Add a' does not update cache on 
                    (* since l is evict-add consistent *)
                    assert (v = last_evict_value_or_init l' a);
      
                    let f_a = is_add_of_addr a in
                    let f_e = is_evict_of_addr a in
                    
                    lemma_last_index_correct2 f_a l (n - 1);
                    assert(last_add_idx l a = n - 1);

                    if has_some_evict l a then
                      (* a has been previously added and evicted *)                        
                      let le = last_evict_idx l a in
                      assert (le < n - 1);

                      lemma_last_index_prefix f_e l (n - 1);
                      assert (last_evict_idx l' a = le);
                      assert (v = evict_payload l' le);

                      let l_le = vprefix l le in
                      lemma_prefix_prefix l (n - 1) le;
                      lemma_prefix_index l (n - 1) le;
                      let cache_le = cache_at_end l_le in
                      assert (prefix l le = prefix l' le);
                      assert (is_evict l le);
                      lemma_evict_requires_cache l le;
                      assert (cache_contains cache_le a);
                      assert (evict_payload l' le == Some?.v (cache_le a));
                      assert (v = Some?.v (cache_le a));

                      //lemma_last_evict_or_init_of_child_unchanged l' (LeftChild a);
                      admit()
                    else
                      admit()
      | Evict a' -> admit()
      | MemoryOp o -> 
        admit()
    

(* Identify the smallest non-evict-add consistent prefix *)
let first_non_eac_prefix (l:verifiable_log {~(evict_add_consistent l)})
  : Tot (i:seq_index l{evict_add_consistent (vprefix l i) /\
                       (is_add l i && 
                        add_payload l i <> last_evict_value_or_init (vprefix l i)
                                                                   (add_addr l i))}) = admit()

(* 
 * Core lemma of part II: if l is verifiable but is not evict-add consistent, then 
 * we can produce a hash collision
 *)
let lemma_not_eac_implies_hash_collision 
  (l:verifiable_log {~ (evict_add_consistent l) })  
  : Tot hash_collision =
  let i = first_non_eac_prefix l in
  (* l_eac is the largest evict-add consistent prefix of l *)
  let l_eac = vprefix l i in
  let a = add_addr l i in

  (* a cannot be the merkle root since a root is never added *)
  if is_merkle_root a then (
    lemma_root_never_added l i;
    (* contradiction *)
    Collision (MkLeaf Null) (MkLeaf Null)
  ) 
  else (
    let cache = cache_at_end l_eac in

    match a with
    (* Case A: a is a left child *)
    | LeftChild p ->

      (* parent p of a is in cache, otherwise the add fails *)
      lemma_add_requires_parent_in_cache l i;
      assert (cache_contains cache p);

      (* 
       * since l_eac is evict-add-consistent, the payload of p 
       * reflects the last evict of a or null 
       *)
      if MkInternal?.left (Some?.v (cache p)) <> hashfn (last_evict_value_or_init l_eac a) then
        lemma_eac_implies_cache_is_last_evict l_eac p
      else (
        assert (MkInternal?.left (Some?.v (cache p)) = hashfn (last_evict_value_or_init l_eac a));
        assert (add_payload l i <> last_evict_value_or_init l_eac a);

        (* 
         * prefix including the add operation does not fail 
         * verification since the full sequence l does not fail
         * verification. *)
        lemma_verifiable_implies_prefix_verifiable l (i + 1);
        lemma_prefix_prefix l (i + 1) i;
        lemma_prefix_index l (i + 1) i;
        assert (Valid? (verifier_step (index l i) (Valid cache)));

        (* Since the parent hash check passes, it follows that ... *)
        assert (hashfn (add_payload l i) = MkInternal?.left (Some?.v (cache p)));      

        (* this implies the following hash collision *)
        Collision (add_payload l i) (last_evict_value_or_init l_eac a)
      )
    (* Symmetric case of right child *)
    | RightChild p -> 

      (* parent p of a is in cache, otherwise the add fails *)
      lemma_add_requires_parent_in_cache l i;
      assert (cache_contains cache p);

      (* 
       * since l_eac is evict-add-consistent, the payload of p 
       * reflects the last evict of a or null 
       *)
      if MkInternal?.right (Some?.v (cache p)) <> hashfn (last_evict_value_or_init l_eac a) then
        lemma_eac_implies_cache_is_last_evict l_eac p
      else (
        assert (MkInternal?.right (Some?.v (cache p)) = hashfn (last_evict_value_or_init l_eac a));
        assert (add_payload l i <> last_evict_value_or_init l_eac a);

        (* 
         * prefix including the add operation does not fail 
         * verification since the full sequence l does not fail
         * verification. *)
        lemma_verifiable_implies_prefix_verifiable l (i + 1);
        lemma_prefix_prefix l (i + 1) i;
        lemma_prefix_index l (i + 1) i;
        assert (Valid? (verifier_step (index l i) (Valid cache)));

        (* Since the parent hash check passes, it follows that ... *)
        assert (hashfn (add_payload l i) = MkInternal?.right (Some?.v (cache p)));      

        (* this implies the following hash collision *)
        Collision (add_payload l i) (last_evict_value_or_init l_eac a)
     )
  )

let lemma_merkle_verifier_correct (l:verifiable_log {not (rw_consistent (memory_ops_of l))}):
  Tot hash_collision = 
  if is_evict_add_consistent l then (
    (* 
     * if l is evict-add consistent then we know 
     * memory_ops of l is rw-consistent, a contradiction
     *)
    lemma_eac_implies_rw_consistency l;
    Collision (MkLeaf Null) (MkLeaf Null)
  )
  else 
    lemma_not_eac_implies_hash_collision l
