module Veritas.MerkleVerifier

open FStar.Seq
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

type vl_index (l:verifier_log) = seq_index l

let is_evict (l:verifier_log) (i:vl_index l): Tot bool =
  Evict? (index l i)

let evict_addr (l:verifier_log) (i:vl_index l{is_evict l i}): Tot merkle_addr = 
  Evict?.a (index l i)

let is_add (l:verifier_log) (i:vl_index l) = 
  Add? (index l i)

let add_addr (l:verifier_log) (i:vl_index l{is_add l i}): Tot merkle_addr = 
  Add?.a (index l i)

let add_payload (l:verifier_log) (i:vl_index l {is_add l i}): Tot merkle_payload =
  Add?.v (index l i)

let is_memory_op (l:verifier_log) (i:vl_index l): Tot bool = MemoryOp? (index l i)

let memory_op_at (l:verifier_log) (i:vl_index l{is_memory_op l i}) = MemoryOp?.o (index l i)

let is_write_op (l:verifier_log) (i:vl_index l): Tot bool = 
  is_memory_op l i && Write? (memory_op_at l i)

let written_value (l:verifier_log) (i:vl_index l{is_write_op l i}): Tot payload = 
  Write?.v (memory_op_at l i)

let is_read_op (l:verifier_log) (i:vl_index l): Tot bool = 
  is_memory_op l i && Read? (memory_op_at l i)

let read_value (l:verifier_log) (i:vl_index l{is_read_op l i}): Tot payload = 
  Read?.v (memory_op_at l i)

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
        if cache_contains cache a then 
          Failed
        else if (is_merkle_leaf a && MkLeaf? v || not (is_merkle_leaf a) && MkInternal? v) then
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
    let l' = prefix l (n - 1) in
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


let verifiable (l:verifier_log): Tot bool = 
  Valid? (verifier l)

type verifiable_log = l:verifier_log{verifiable l}

let rec verifiable_implies_prefix_verifiable (l:verifiable_log) (i:nat{i <= length l}):
  Lemma (requires (True))
        (ensures (verifiable (prefix l i)))
        (decreases (length l)) = 
  let n = length l in
  if n = 0 then ()
  else if i = n then lemma_fullprefix_equal l
  else ( 
    verifiable_implies_prefix_verifiable (prefix l (n - 1)) i;
    lemma_prefix_prefix l (n - 1) i
  )

let vprefix (l:verifiable_log) (i:nat{i <= length l}): Tot verifiable_log = 
  verifiable_implies_prefix_verifiable l i;prefix l i

let evict_payload (l:verifiable_log) (i:vl_index l{is_evict l i}): 
  Tot (merkle_payload_of_addr (evict_addr l i)) =
  verifiable_implies_prefix_verifiable l (i + 1);
  verifiable_implies_prefix_verifiable l i;
  let a = evict_addr l i in
  let l'' = prefix l i in
  let vs'' = verifier l'' in 
  lemma_prefix_prefix l (i + 1) i;
  lemma_prefix_index l (i + 1) i;
  Some?.v ((Valid?.vc vs'') a)
  
let is_evict_of_addr (a:merkle_addr) (e:verifier_log_entry) = 
  Evict? e && Evict?.a e = a

let last_evict_idxopt (l:verifier_log) (a:merkle_addr) = last_index_opt (is_evict_of_addr a) l

let has_some_evict (l:verifier_log) (a:merkle_addr) = exists_sat_elems (is_evict_of_addr a) l

let last_evict_idx (l:verifier_log) (a:merkle_addr{has_some_evict l a}) = 
  last_index (is_evict_of_addr a) l

let last_evict_value_or_null (l:verifiable_log) (a:merkle_leaf_addr): 
  Tot (merkle_payload_of_addr a) = 
  if has_some_evict l a then
    evict_payload l (last_evict_idx l a)
  else
    MkLeaf Null

type evict_add_consistent  = l:verifiable_log {forall (i:vl_index l). 
    is_add l i /\ is_merkle_leaf (add_addr l i) ==> 
    add_payload l i = last_evict_value_or_null (vprefix l i) (add_addr l i)}

let is_write_to_addr (a:merkle_leaf_addr) (e:verifier_log_entry) = 
  MemoryOp? e && is_write_to_addr (merkle_leaf_to_addr a) (MemoryOp?.o e)

let last_write_idxopt (l:verifiable_log) (a:merkle_leaf_addr) = last_index_opt (is_write_to_addr a) l

let has_some_write (l:verifiable_log) (a:merkle_leaf_addr) = exists_sat_elems (is_write_to_addr a) l

let last_write_idx (l:verifiable_log) (a:merkle_leaf_addr{has_some_write l a}) = 
  last_index (is_write_to_addr a) l

let cache_at_end (l:verifiable_log): Tot verifier_cache = 
  Valid?.vc (verifier l)

let last_write_value_or_null (l:verifiable_log) (a:merkle_leaf_addr): Tot (merkle_payload_of_addr a) =
  if has_some_write l a then
    MkLeaf (written_value l (last_write_idx l a))
  else
    MkLeaf Null

let is_add_of_addr (a:merkle_addr) (e:verifier_log_entry) = 
  Add? e && Add?.a e = a

let last_add_idxopt (l:verifier_log) (a:merkle_addr) = last_index_opt (is_add_of_addr a) l

let has_some_add (l:verifier_log) (a:merkle_addr) = exists_sat_elems (is_add_of_addr a) l

let last_add_idx (l:verifier_log) (a:merkle_addr{has_some_add l a}) = 
  last_index (is_add_of_addr a) l

let rec lemma_evict_between_adds (l:verifiable_log) 
                                 (i1:vl_index l{is_add l i1}) 
                                 (i2:vl_index l{is_add l i2 && add_addr l i1 = add_addr l i2 && i2 > i1}):
  Lemma (requires (True))
        (ensures (has_some_evict (prefix l i2) (add_addr l i2) && 
                  last_evict_idx (prefix l i2) (add_addr l i2) > i1))
        (decreases (length l)) = admit()

let rec lemma_add_between_evicts (l:verifiable_log)
                                 (i1:vl_index l{is_evict l i1})
                                 (i2:vl_index l{is_evict l i2 && evict_addr l i1 = evict_addr l i2 && i2 > i1}):
  Lemma (requires (True))
        (ensures (has_some_add (prefix l i2) (evict_addr l i2) &&
                  last_add_idx (prefix l i2) (evict_addr l i2) > i1))
        (decreases (length l)) = admit()

let lemma_memop_requires_cache (l:verifiable_log) (i:vl_index l):
  Lemma (requires (is_memory_op l i))
        (ensures  (cache_contains (cache_at_end (vprefix l i)) 
                                  (addr_to_merkle_leaf (address_of (memory_op_at l i))))) = admit()

let lemma_evict_requires_cache (l:verifiable_log) (i:vl_index l):
  Lemma (requires (is_evict l i))
        (ensures  (cache_contains (cache_at_end (vprefix l i)) (evict_addr l i))) = admit()

let rec lemma_cache_contains_implies_last_add_before_evict (l:verifiable_log) (a:merkle_non_root_addr):
  Lemma (requires (cache_contains (cache_at_end l) a))
        (ensures (has_some_add l a /\
                  (has_some_evict l a ==> last_evict_idx l a < last_add_idx l a)))
        (decreases (length l)) = admit()

let rec lemma_last_add_before_evict_implies_cache_contains (l:verifiable_log) (a:merkle_non_root_addr):
  Lemma (requires (has_some_add l a /\
                   (has_some_evict l a ==> last_evict_idx l a < last_add_idx l a)))
        (ensures (cache_contains (cache_at_end l) a))
        (decreases (length l)) = admit()

(* Does this log entry update the cache for address a *)
let updates_cache (a:merkle_addr) (e:verifier_log_entry): Tot bool = 
  match e with
  | MemoryOp o -> Write? o && addr_to_merkle_leaf (address_of o) = a
  | Add a' v -> a = a' 
  | Evict a' -> a = a'

(* The state of the cache is unchanged on a verifier step if the log entry does not update the cache *)
let lemma_updates_cache (vc:verifier_cache) (a:merkle_addr) (e:verifier_log_entry):
  Lemma (requires (Valid? (verifier_step e (Valid vc)) && not (updates_cache a e) && cache_contains vc a))
        (ensures (cache_contains (Valid?.vc (verifier_step e (Valid vc))) a && 
                  Some?.v (vc a) = Some?.v (Valid?.vc (verifier_step e (Valid vc)) a))) = admit()

(* The state of the cache is unchanged on a verifier step if the log entry does not update the cache *)
let lemma_updates_cache_inv (vc:verifier_cache) (a:merkle_addr) (e:verifier_log_entry):
  Lemma (requires (Valid? (verifier_step e (Valid vc)) && not (updates_cache a e) && 
                   cache_contains (Valid?.vc (verifier_step e (Valid vc))) a))
        (ensures (cache_contains vc a && 
                  Some?.v (vc a) = Some?.v (Valid?.vc (verifier_step e (Valid vc)) a))) = admit()

(* If the last entry of the log does not write to a, then last_write_value remains unchanged *)
let lemma_last_write_unchanged_unless_write (l:verifiable_log{length l > 0}) (a:merkle_leaf_addr):
  Lemma (requires (not (is_write_to_addr a (index l (length l - 1)))))
        (ensures (last_write_value_or_null l a = last_write_value_or_null (prefix l (length l - 1)) a)) =
  admit()        

let rec lemma_eac_implies_cache_is_last_write (l:evict_add_consistent) (a:merkle_leaf_addr):
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
    let aux2 (i:vl_index l) (j:vl_index (prefix l i)):
      Lemma (is_add (prefix l i) j /\ is_merkle_leaf (add_addr (prefix l i) j) ==>
             add_payload (prefix l i) j = last_evict_value_or_null (vprefix (vprefix l i) j) 
                                                                   (add_addr (prefix l i) j)) = 
      let l' = vprefix l i in
      if not (is_add l' j) then ()
      else if not (is_merkle_leaf (add_addr l' j)) then ()
      else (
        lemma_prefix_index l i j;
        assert (is_add l' j);
        lemma_prefix_prefix l i j;
        assert(vprefix l j = vprefix l' j)
      )
    in
    (* Induction step on l' *)
    let l' = prefix l (n - 1) in
    forall_intro (aux2 (n - 1)); 
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
          assert (v = last_evict_value_or_null l' a);

          (* Case A: there was a previous Evict a *)
          if has_some_evict l a then (
            let lei = last_evict_idx l a in
            let l_lei_pre = vprefix l lei in
            
            (* Apply induction at lei *)
            forall_intro (aux2 lei); 
            lemma_eac_implies_cache_is_last_write l_lei_pre a;                

            (* cache at lei *)
            let cache_lei_pre = (cache_at_end l_lei_pre) in

            (* since lei is an evict, cache_lei_pre should contain a *)
            lemma_evict_requires_cache l lei;
            assert(cache_contains cache_lei_pre a);

            (* from induction ... *)
            assert(Some?.v (cache_lei_pre a) = last_write_value_or_null l_lei_pre a);

            admit()
          )
          (* Case B: there was no previous Evict a *)
          else (
            (* l does not have evict => l' does not have an evict *)
            let f = is_evict_of_addr a in
            lemma_not_exists_prefix f l (n - 1);
            assert (not (has_some_evict l' a));

            (* this implies .... *)
            assert (last_evict_value_or_null l' a = MkLeaf Null);
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
        
        (* Add a' <> a handled earlier (not updates cache) *)
        else ()

      | MemoryOp o ->
      admit()
    )
  )

(*

    let cache = cache_at_end l in
    let l' = prefix l (n - 1) in
    let e = index l (n - 1) in
    let cache' = cache_at_end l' in
    let f = is_write_to_addr a in
    let aux (i:vl_index l'):
      Lemma (is_add l' i /\ is_merkle_leaf (add_addr l' i) ==>
             add_payload l' i = last_evict_value_or_null (vprefix l' i) (add_addr l' i)) = 
      if not (is_add l' i) then ()
      else if not (is_merkle_leaf (add_addr l' i)) then ()
      else (
        lemma_prefix_index l (n - 1) i;
        assert(is_add l' i);
        lemma_prefix_prefix l (n - 1) i;
        assert(vprefix l i = vprefix l' i)
      )
    in
    forall_intro aux; 
    lemma_eac_implies_cache_is_last_write l' a;    
    if not (cache_contains (cache_at_end l) a) then ()  
    else match e with 
    | MemoryOp o -> 
      assert (cache_contains cache' (addr_to_merkle_leaf (address_of o)));
      if (Read? o) then (
        if has_some_write l' a then (
          let li' = last_write_idx l' a in
          lemma_prefix_index l (n - 1) li';
          lemma_last_index_correct2 f l li';
          let li = last_write_idx l a in
          lemma_prefix_index l (n - 1) li;
          if li = li' then ()
          else if li < li' then
            lemma_last_index_correct1 f l li'
          else // li > li' 
            lemma_last_index_correct1 f l' li
        )
        else (
          if has_some_write l a then (
            let li = last_write_idx l a in
            lemma_prefix_index l (n - 1) li;
            lemma_last_index_correct2 f l' li
          )
          else ()
        )
      )
      else if a = addr_to_merkle_leaf (Write?.a o) then (
        lemma_merkle_equal_implies_addr_equal (merkle_leaf_to_addr a) (Write?.a o);
        lemma_last_index_correct2 f l (n - 1)        
      )
      else (
        assert (not (f e));
        if has_some_write l' a then (
          let li' = last_write_idx l' a in
          lemma_prefix_index l (n - 1) li';
          lemma_last_index_correct2 f l li';
          let li = last_write_idx l a in
          lemma_prefix_index l (n - 1) li;
          if li = li' then ()
          else if li < li' then
            lemma_last_index_correct1 f l li'
          else // li > li' 
            lemma_last_index_correct1 f l' li        
        )
        else (
          if has_some_write l a then (
            let li = last_write_idx l a in
            lemma_prefix_index l (n - 1) li;
            lemma_last_index_correct2 f l' li
          )
          else ()         
        )
      )
    | Evict a' -> 
        if has_some_write l' a then (
          let li' = last_write_idx l' a in
          lemma_prefix_index l (n - 1) li';
          lemma_last_index_correct2 f l li';
          let li = last_write_idx l a in
          lemma_prefix_index l (n - 1) li;
          if li = li' then ()
          else if li < li' then
            lemma_last_index_correct1 f l li'
          else // li > li' 
            lemma_last_index_correct1 f l' li
        )
        else (
          if has_some_write l a then (
            let li = last_write_idx l a in
            lemma_prefix_index l (n - 1) li;
            lemma_last_index_correct2 f l' li
          )
          else ()
        )        
    | Add a' v -> 
      if a' = a then (
        if cache_contains cache' a then () // verifier fails -><-
        else (
          let f' = is_evict_of_addr a in
          if has_some_evict l a then            
            admit()
          else (  
            lemma_not_exists_prefix f' l (n - 1);
            assert(not (has_some_evict l' a));
            assert(is_add l (n - 1));
            assert(is_merkle_leaf a);
            assert(v = last_evict_value_or_null l' a);
            assert(v = MkLeaf Null);
            if has_some_write l a then          
            (                            
              let li = last_write_idx l a in
              let w = index l li in // last write
              let llw = vprefix l li in // log at last write
              let vslw = verifier llw in // verifier state before last write
              assert (Valid? vslw);
              let vs_after_lw = verifier_step w vslw in
              lemma_prefix_prefix l (li + 1) li;
              let log_after_lw = vprefix l (li + 1) in
              assert (verifiable log_after_lw);
              let vs_after_lw' = verifier log_after_lw in
              assert (Valid? vs_after_lw');
              lemma_prefix_index l (li + 1) li;
              assert (vs_after_lw' == verifier_step w vslw);
              assert (vs_after_lw' == vs_after_lw);
              assert (Valid? vs_after_lw);
              assert(addr_to_merkle_leaf (Write?.a (MemoryOp?.o w)) = a);
              let cache_before_lw = Valid?.vc vslw in
              assert (cache_contains cache_before_lw a);
              //assert (cache_contains cache_at_last_write a);
              admit()
            )
            else 
              lemma_not_exists_prefix f l (n - 1)            
          )
        )
      )
      else (
        assert(cache_contains cache a);
        assert(cache_contains cache' a);
        assert(Some?.v (cache a) = Some?.v (cache' a));
        assert (not (f e));        
        if has_some_write l' a then (
          let li' = last_write_idx l' a in
          lemma_prefix_index l (n - 1) li';
          lemma_last_index_correct2 f l li';
          let li = last_write_idx l a in
          lemma_prefix_index l (n - 1) li;
          if li = li' then ()
          else if li < li' then
            lemma_last_index_correct1 f l li'
          else // li > li' 
            lemma_last_index_correct1 f l' li
        )
        else (
          if has_some_write l a then (
            let li = last_write_idx l a in
            lemma_prefix_index l (n - 1) li;
            lemma_last_index_correct2 f l' li
          )
          else ()
        )        
      )*)

   
(*
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



let last_write_value_or_null (l:verifiable_log) (ma:merkle_leaf_addr): Tot merkle_payload =
  let ml = project_memory_log l in
  let a = merkle_leaf_to_addr ma in
  if has_some_write ml a then
    MkLeaf (last_write_value ml a)
  else
    MkLeaf Null
      
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
*)
