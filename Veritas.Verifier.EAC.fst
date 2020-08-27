module Veritas.Verifier.EAC

open FStar.Seq
open Veritas.BinTree
open Veritas.EAC
open Veritas.Hash
open Veritas.Interleave
open Veritas.Key
open Veritas.MultiSet
open Veritas.MultiSetHash
open Veritas.Record
open Veritas.SeqAux
open Veritas.SeqMachine
open Veritas.State
open Veritas.Verifier
open Veritas.Verifier.Blum
open Veritas.Verifier.CorrectDefs
open Veritas.Verifier.Merkle
open Veritas.Verifier.TSLog

module EC = Veritas.EAC
module MS = Veritas.MultiSet
module MH = Veritas.MultiSetHash
module V = Veritas.Verifier

(* generalized single- and multi-set hash collision *)
type hash_collision_gen =
  | SingleHashCollision: hc: hash_collision -> hash_collision_gen
  | MultiHashCollision: hc: ms_hash_collision -> hash_collision_gen

(* construct a hash collision from a contradiction *)
let hash_collision_contra (_:unit{False}): hash_collision_gen = 
  SingleHashCollision (Collision (DVal Null) (DVal Null))

let max_eac_ts_prefix (#p:pos) (itsl: non_eac_ts_log p): eac_ts_log p =
  let tsle = time_seq_ext itsl in
  let i = max_eac_prefix tsle in
  its_prefix itsl i

(* the entry that causes the eac_invalidation *)
let invalidating_log_entry (#n:pos) (itsl: non_eac_ts_log n): vlog_entry_ext = 
  let tsle = time_seq_ext itsl in  
  let i = max_eac_prefix tsle in  
  index tsle i

(* the key that causes the eac_invalidation *)
let eac_invalidating_key (#n:pos) (itsl: non_eac_ts_log n): key =
  vlog_entry_ext_key (invalidating_log_entry itsl)

(* last valid eac state *)
let last_valid_eac_state (#n:pos) (itsl: non_eac_ts_log n): eac_state = 
  let tsle = time_seq_ext itsl in  
  let i = max_eac_prefix tsle in
  let k = eac_invalidating_key itsl in
  eac_state_of_key (its_prefix itsl i) k
  
(* applying the invalidating entry on the last valid state produces EAC failure *)
let lemma_invalidation (#n:pos) (itsl: non_eac_ts_log n):
  Lemma (requires True)
        (ensures (EACFail <> last_valid_eac_state itsl /\
                  EACFail = eac_add (invalidating_log_entry itsl) (last_valid_eac_state itsl)))
        [SMTPat (last_valid_eac_state itsl)]
        =            
  let tsl = project_seq itsl in
  let tsle = time_seq_ext itsl in
  
  let i = max_eac_prefix tsle in

  (* maximum eac prefix *)
  let tslei = prefix tsle i in

  (* minimum non-eac prefix *)
  let tslei' = prefix tsle (i + 1) in

  lemma_first_invalid_key eac_sm tsle;

  (* ee is the entry causing eac invalidation *)
  let ee = index tsle i in
  assert(ee = invalidating_log_entry itsl);

  (* the key causing the invalidation *)
  let k = eac_invalidating_key itsl in

  (* log entries of only key k *)
  let tslek = partn eac_sm k tsle in

  (* j the index in tslek causing invalidation *)
  let j = max_valid_prefix eac_smk tslek in
  //assert(filter_index_inv_map (iskey vlog_entry_key k) tsle i = j);  
  //assert(vlog_entry_key ee = k);
  //assert(index tslek j = ee);

  let tslekj = prefix tslek j in
  assert(valid eac_smk tslekj);  

  let st = seq_machine_run eac_smk tslekj in
  assert(st <> EACFail);

  // filtering out k-entries in tslei is the as taking the prefix j in tslekj
  lemma_filter_prefix_comm (iskey vlog_entry_ext_key k) tsle i;
  assert(st = last_valid_eac_state itsl);

  lemma_reduce_prefix EACInit eac_add (prefix tslek (j + 1)) j;  
  lemma_reduce_singleton st eac_add (suffix (prefix tslek (j + 1)) 1);
  assert(eac_add ee st = EACFail);

  ()         

let lemma_verifier_thread_state_extend (#n:pos) (itsl: its_log n{length itsl > 0}):
  Lemma (verifier_thread_state itsl (its_thread_id itsl (length itsl - 1)) == 
         t_verify_step (verifier_thread_state (its_prefix itsl (length itsl - 1)) 
                                              (its_thread_id itsl (length itsl - 1)))
                       (its_vlog_entry itsl (length itsl - 1))) = 
  let m = length itsl in
  let id = its_thread_id itsl (m - 1) in
  let e = its_vlog_entry itsl (m - 1) in
  let itsl' = its_prefix itsl (m - 1) in
  let gl' = partition_idx_seq itsl' in
  lemma_partition_idx_extend1 itsl;
  lemma_prefix1_append (index gl' id) e

let lemma_time_seq_ext_correct (#n:pos) (itsl: its_log n) (i:seq_index itsl):
  Lemma (requires True)
        (ensures (its_vlog_entry itsl i = to_vlog_entry (index (time_seq_ext itsl) i))) 
        [SMTPat (to_vlog_entry (index (time_seq_ext itsl) i))] =
  lemma_project_seq_index itsl i

(* if an operation requires the key in store, it cannot be the first operation *)
let lemma_non_eac_init_requires_key_in_store (#n:pos) 
  (itsl: non_eac_ts_log n{last_valid_eac_state itsl = EACInit /\
                           requires_key_in_store (to_vlog_entry (invalidating_log_entry itsl)) /\
                           Root <> vlog_entry_key (to_vlog_entry (invalidating_log_entry itsl))}):  
  hash_collision_gen = 
  let tsle = time_seq_ext itsl in
  let i = max_eac_prefix tsle in
  let itsli = its_prefix itsl i in
  let itsli' = its_prefix itsl (i + 1) in
  let tid = its_thread_id itsl i in
  let e = its_vlog_entry itsl i in
  assert(e = its_vlog_entry itsli' (length itsli' - 1));
  lemma_verifier_thread_state_extend itsli';
  //assert(verifier_thread_state itsli' tid == t_verify_step (verifier_thread_state itsli tid) e);
  let k = vlog_entry_key e in
  lemma_eac_state_init_store itsli k tid;
  hash_collision_contra ()


(* the first operation for a key cannot be evict *)
let lemma_non_eac_init_evict (#n:pos)
  (itsl: non_eac_ts_log n{last_valid_eac_state itsl = EACInit /\
                           requires_key_in_store (to_vlog_entry (invalidating_log_entry itsl)) /\
                           V.is_evict (to_vlog_entry (invalidating_log_entry itsl))}): hash_collision_gen =
  let tsle = time_seq_ext itsl in
  let i = max_eac_prefix tsle in
  let itsli = its_prefix itsl i in
  let itsli' = its_prefix itsl (i + 1) in
  let tid = its_thread_id itsl i in  
  let e = its_vlog_entry itsl i in  
  lemma_verifier_thread_state_extend itsli';
  let k = vlog_entry_key e in
  lemma_root_never_evicted (verifier_thread_state itsli tid) e;  
  assert(k <> Root);                               
  lemma_non_eac_init_requires_key_in_store itsl

(* 
 * if the key is in an EACInit state at the end of itsl, then 
 * there cannot be an log entries with key k 
 *)
let lemma_eac_init_implies_no_key_entries 
  (#n:pos)
  (itsl: its_log n)
  (k:key):
  Lemma (requires (eac_state_of_key itsl k = EACInit))
        (ensures (not (has_some_entry_of_key itsl k))) = 
  let tsle = time_seq_ext itsl in          

  (* partition of log stream of key k *)
  let tslek = partn eac_sm k tsle in
  assert(seq_machine_run eac_smk tslek = EACInit);

  (* partition is of length 0 *)
  lemma_notempty_implies_noninit eac_smk tslek;
  assert(length tslek = 0);

  if has_some_entry_of_key itsl k then (  
    (* if there is some entry of key k, we can find an index into tslek, a contradiction *)
    let i = last_index (entry_of_key k) itsl in
    let j = filter_index_inv_map (iskey vlog_entry_ext_key k) tsle i in  
    ()
  )
  else ()

(* the first operation for a key cannot be a blum add *)
let lemma_non_eac_init_addb (#n)
  (itsl: non_eac_ts_log n{
    g_hash_verifiable (partition_idx_seq itsl) /\
    last_valid_eac_state itsl = EACInit /\
                          AddB? (to_vlog_entry (invalidating_log_entry itsl))}): hash_collision_gen =
  (* hash verifiable - evict hash and add hash equal *)                          
  let gl = partition_idx_seq itsl in                           
  assert(g_hadd gl = g_hevict gl);

  let tsle = time_seq_ext itsl in
  let i = max_eac_prefix tsle in
  let (e,tid) = index itsl i in
  let k = vlog_entry_key e in

  (* the i'th entry is a blum add *)
  assert(is_blum_add (index itsl i));
  let be = blum_add_elem (index itsl i) in
  
  (* pre-condition: state of key after processing i entries i EACInit *)
  let itsli = its_prefix itsl i in
  assert(eac_state_of_key itsli k = EACInit);

  (* the first i entries cannot contain any entry with key k *)
  lemma_eac_init_implies_no_key_entries itsli k;
  assert(not (has_some_entry_of_key itsli k));

  (* if the add element be is in the evict set *)
  if contains be (ts_evict_set itsl) then (
    (* the evict that corresponds to blum add happens before i *)
    let j = index_blum_evict itsl be in
    lemma_evict_before_add itsl i;
    assert(j < i);

    (* this emplies itsli contains an entry with key k *)
    (* a contradiction *)
    lemma_last_index_correct2 (entry_of_key k) itsli j;
    
    hash_collision_contra ()                           
  )
  else (  
    lemma_add_elem_correct itsl i;
    lemma_ts_add_set_correct itsl;
    lemma_ts_evict_set_correct itsl;

    assert(contains be (ts_add_set itsl));
    assert(not (contains be (ts_evict_set itsl)));
    
    lemma_ts_add_set_correct itsl;
    lemma_ts_evict_set_correct itsl;

    assert(ts_add_set itsl == g_add_set gl);
    assert(ts_evict_set itsl == g_evict_set gl);
    MS.lemma_not_equal (g_add_set gl) (g_evict_set gl) be;    
    assert(~ (g_add_set gl == g_evict_set gl));

    lemma_g_hadd_correct gl;
    lemma_ghevict_correct gl;

    MultiHashCollision (MSCollision (g_add_seq gl) (g_evict_seq gl))
  )

let lemma_non_eac_init_addm
  (#p:pos) 
  (itsl: non_eac_ts_log p{
    last_valid_eac_state itsl = EACInit /\
    AddM? (to_vlog_entry (invalidating_log_entry itsl))
   })
   : hash_collision_gen =
   
  let st = last_valid_eac_state itsl in   
  let ee = invalidating_log_entry itsl in
  assert(eac_add ee st = EACFail);

  let tsle = time_seq_ext itsl in
  let i = max_eac_prefix tsle in
  let (e,tid) = index itsl i in
  assert(to_vlog_entry ee = e);

  let itsli = its_prefix itsl i in
  let vsi = verifier_thread_state itsli tid in
  let itsli' = its_prefix itsl (i+1) in
  let vsi' = verifier_thread_state itsli' tid in
  
  lemma_verifier_thread_state_extend itsli';  
  assert(vsi' == t_verify_step vsi e);
  match e with
  | AddM (k,v) k' -> 
    (* otherwise eac_add ee st <> EACFail *)
    assert(v <> init_value k);

    (* verifier checks this *)
    assert(is_proper_desc k k');

    (* k' is the proving ancestor of k*)
    lemma_addm_ancestor_is_proving itsli';
    assert(k' = proving_ancestor itsli k);

    (* k' is the verifier cache *)
    assert(store_contains (thread_store vsi) k');
    lemma_eac_value_is_stored_value itsli k' tid;
    assert(eac_value itsli k' = stored_value (thread_store vsi) k');

    let v' = eac_merkle_value itsli k' in
    assert(v' = to_merkle_value( stored_value (thread_store vsi) k'));
    let d = desc_dir k k' in
    let dh' = desc_hash_dir v' d in

    (* k' points to none or some non-ancestor of k *)
    assert(is_eac_state_init itsli k);
    lemma_proving_ancestor_initial itsli k;

    assert(mv_points_to_none v' d \/ 
          not (is_desc k (mv_pointed_key v' d)));

    match dh' with
    | Empty -> hash_collision_contra()
    | Desc k2 _ _ -> 
      assert(not (is_desc k k2));
      lemma_desc_reflexive k;
      assert(k <> k2);
      hash_collision_contra()

let lemma_non_eac_instore_get (#p:pos)   
  (itsl: non_eac_ts_log p{
    EACInStore? (last_valid_eac_state itsl)  /\
    Get? (to_vlog_entry (invalidating_log_entry itsl))
   })
  : hash_collision_gen = 
  let st = last_valid_eac_state itsl in   
  let ee = invalidating_log_entry itsl in
  assert(eac_add ee st = EACFail);

  let tsle = time_seq_ext itsl in
  let i = max_eac_prefix tsle in
  let (e,tid) = index itsl i in
  assert(to_vlog_entry ee = e);

  let itsli = its_prefix itsl i in
  let vsi = verifier_thread_state itsli tid in
  let itsli' = its_prefix itsl (i+1) in
  let vsi' = verifier_thread_state itsli' tid in
  
  lemma_verifier_thread_state_extend itsli';  
  assert(vsi' == t_verify_step vsi e);

  match st with 
  | EACInStore m v -> (
    match ee with 
    | NEvict (Get k v') -> 
      (* otherwise there will not be an eac failure *)
      assert(DVal v' <> v);

      (* the thread id where k was last added *)
      let tid_add = last_add_tid itsli k in

      (* we expect the get operation to go to tid of last add *)
      if tid_add = tid then (
        lemma_eac_state_instore itsli k;

        (* the stored value of k = v <> v' *)
        assert(stored_value (thread_store vsi) k = v);

        (* this implies a verification failure, a contradiction *)
        hash_collision_contra()
      )
      else (
        (* if the get goes to tid <> tid_add, then the cache of tid does not contain k *)   
        lemma_eac_state_instore2 itsli k tid;
        assert(not (store_contains (thread_store vsi) k));

        (* this implies that verification fails on get, a contradiction *)
        hash_collision_contra()
      )
  )

let lemma_non_eac_instore_put (#p:pos)   
  (itsl: non_eac_ts_log p{
    EACInStore? (last_valid_eac_state itsl)  /\
    Put? (to_vlog_entry (invalidating_log_entry itsl))
   })
  : hash_collision_gen = 
  let st = last_valid_eac_state itsl in   
  let ee = invalidating_log_entry itsl in
  assert(eac_add ee st = EACFail);

  let tsle = time_seq_ext itsl in
  let i = max_eac_prefix tsle in
  let (e,tid) = index itsl i in
  assert(to_vlog_entry ee = e);

  let itsli = its_prefix itsl i in
  let vsi = verifier_thread_state itsli tid in
  let itsli' = its_prefix itsl (i+1) in
  let vsi' = verifier_thread_state itsli' tid in
  
  lemma_verifier_thread_state_extend itsli';  
  assert(vsi' == t_verify_step vsi e);

  match st with 
  | EACInStore m v -> (
    match ee with 
    | NEvict (Put k v') -> 
      assert(not (DVal? v));

      (* the thread id where k was last added *)
      let tid_add = last_add_tid itsli k in

      (* the store of tid_add contains the value of key k *)
      lemma_eac_state_instore itsli k;

      (* the store ensures the values are consistent with key types;
       * this implies (DVal? v), a contradiction *)
      assert(DVal? v);

      hash_collision_contra()
  )

let lemma_non_eac_instore_addb (#p:pos)   
  (itsl: non_eac_ts_log p{
    g_hash_verifiable (partition_idx_seq itsl) /\
    EACInStore? (last_valid_eac_state itsl)  /\
    AddB? (to_vlog_entry (invalidating_log_entry itsl))
   })
  : hash_collision_gen = 
  (* hash verifiable - evict hash and add hash equal *)                          
  let gl = partition_idx_seq itsl in                           
  assert(g_hadd gl = g_hevict gl);

  let st = last_valid_eac_state itsl in   
  let ee = invalidating_log_entry itsl in
  assert(eac_add ee st = EACFail);

  let tsle = time_seq_ext itsl in
  let i = max_eac_prefix tsle in
  let (e,tid) = index itsl i in
  assert(to_vlog_entry ee = e);
  let k = vlog_entry_key e in

  let itsli = its_prefix itsl i in
  let vsi = verifier_thread_state itsli tid in
  let itsli' = its_prefix itsl (i + 1) in

  (* number of blum evicts is the same as blum adds in the first i entries *)
  lemma_evict_add_count_same itsli k;
  assert(MS.size (ts_add_set_key itsli k) = MS.size (ts_evict_set_key itsli k));

  (* the ith element is a blum add *)
  assert(is_blum_add #p (e,tid));
  lemma_ts_add_set_key_extend itsli';
  assert(ts_add_set_key itsli' k == add_elem (ts_add_set_key itsli k)
                                             (blum_add_elem #p (e,tid)));

  (* the ith element is not a blum evict *)
  assert(not (is_blum_evict (index itsl i)));
  lemma_ts_evict_set_key_extend2 itsli';
  assert(ts_evict_set_key itsli' k == ts_evict_set_key itsli k);

  (* this implies that the size of the add set after processing (i+1) elements 
   * is one larger than the evict set at this point *)
  assert(MS.size (ts_add_set_key itsli' k) = 1 + (MS.size (ts_evict_set_key itsli' k)));

  (* this implies that in the first (i+1) entries there is an element whose membership in 
   * add multiset is > its membership in evict multiset *)
  let be = diff_elem (ts_add_set_key itsli' k) (ts_evict_set_key itsli' k) in  
  assert(MS.contains be (ts_add_set_key itsli' k));
  lemma_ts_add_set_key_contains_only itsli' k be;
  assert(MH.key_of be = k);
  lemma_mem_key_add_set_same itsli' be;
  lemma_mem_key_evict_set_same itsli' be;  
  assert(MS.mem be (ts_add_set itsli') > MS.mem be (ts_evict_set itsli'));

  (* the index of be in the add set *)
  let i_be = some_add_elem_idx itsli' be in
  assert(i_be <= i);

  (* from clock orderedness any evict_set entry for be should happen before i *)
  lemma_evict_before_add2 itsl i_be;
  assert(MS.mem be (ts_evict_set itsl) = MS.mem be (ts_evict_set (its_prefix itsl i_be)));

  (* any set membership is monotonic *)
  lemma_mem_monotonic be itsl (i + 1);
  lemma_mem_monotonic be itsli' i_be;
  assert(MS.mem be (ts_add_set itsl) >= MS.mem be (ts_add_set itsli'));
  assert(MS.mem be (ts_evict_set itsl) = MS.mem be (ts_evict_set itsli'));

  (* this implies the membership of be in (overall) addset > membership in evict set *)
  (* so these two sets are not equal providing a hash collision *)
  assert(MS.mem be (ts_add_set itsl) > MS.mem be (ts_evict_set itsl));  

  MS.lemma_not_equal (ts_add_set itsl) (ts_evict_set itsl) be;
  assert(~( (ts_add_set itsl) == (ts_evict_set itsl)));

  lemma_ts_add_set_correct itsl;
  lemma_ts_evict_set_correct itsl;
  assert(~ (g_add_set gl == g_evict_set gl));


  lemma_g_hadd_correct gl;
  lemma_ghevict_correct gl;

  MultiHashCollision (MSCollision (g_add_seq gl) (g_evict_seq gl))

let lemma_non_eac_instore_addm (#p:pos)   
  (itsl: non_eac_ts_log p{
    EACInStore? (last_valid_eac_state itsl)  /\
    AddM? (to_vlog_entry (invalidating_log_entry itsl))
   })
  : hash_collision_gen = 
  let tsle = time_seq_ext itsl in
  let i = max_eac_prefix tsle in  
  let (e,tid) = index itsl i in
  let k = vlog_entry_key e in
  let itsli = its_prefix itsl i in    

  (* verifier thread state of tid after itsli *)
  let vsi = verifier_thread_state itsli tid in
  lemma_eac_state_instore itsli k;

  (* the tid of the last add to k prior to i *)
  let ltid = last_add_tid itsli k in

  let itsli' = its_prefix itsl (i + 1) in
  let vsi' = verifier_thread_state itsli' tid in      
  lemma_verifier_thread_state_extend itsli';    
  assert(vsi' == t_verify_step vsi e);      

  if ltid = tid then (
    (* the store of tid contains the key k already *)
    assert(store_contains (thread_store vsi) k);    

    (* if store of tid already contained k then verifier should fail - a contradiction *)
    hash_collision_contra()
  )
  else (
    match e with
    | AddM _ k' ->

    (* k' is the proving ancestor of k *)
    lemma_addm_ancestor_is_proving itsli';
    assert(k' = proving_ancestor itsli k);

    (* thread store of tid contains k' *)
    assert(store_contains (thread_store vsi) k');

    (* k is present in the store of last add - ltid *)
    assert(store_contains (thread_store (verifier_thread_state itsli ltid)) k);

    (* this implies k' is in the store of ltid *)
    lemma_store_contains_proving_ancestor itsli ltid k;
    assert(store_contains (thread_store (verifier_thread_state itsli ltid)) k');

    if k' = Root then (
      (* the root is never contained in a non-zero thread id, and either ltid or tid is non-zero *)
      assert(ltid <> 0 || tid <> 0);

      if ltid <> 0 then (
        lemma_root_not_in_store itsli ltid;
        hash_collision_contra()
      )
      else (
        lemma_root_not_in_store itsli tid;
        hash_collision_contra()
      )
    )
    else (
      
      lemma_instore_implies_eac_state_instore itsli k' ltid;
      assert(is_eac_state_instore itsli k');
      
      lemma_eac_state_instore itsli k';            

      (* last add thread id of k' *)
      let ltid' = last_add_tid itsli k' in

      if ltid' = ltid then (
        (* this would imply k' is not in store of tid, a contradiction *)
        lemma_eac_state_instore2 itsli k' tid;

        hash_collision_contra()
      )
      else (
        (* this would imply k' is not in the store of ltid, a contradiction *)
        lemma_eac_state_instore2 itsli k' ltid;
        hash_collision_contra()
      )
    )
  )

let lemma_non_eac_instore_evictm (#p:pos)   
  (itsl: non_eac_ts_log p{
    EACInStore? (last_valid_eac_state itsl)  /\
    EvictM? (to_vlog_entry (invalidating_log_entry itsl))
   })
  : hash_collision_gen = 
  let st = last_valid_eac_state itsl in   
  let ee = invalidating_log_entry itsl in
  assert(eac_add ee st = EACFail);

  match st with
  | EACInStore m v -> (
    match ee with
    | EvictMerkle (EvictM k k') v' -> 
      (* otherwise we would not have an eac failure *)
      assert(DVal? v && v' <> v);

      let tsle = time_seq_ext itsl in
      let i = max_eac_prefix tsle in
      let (e,tid) = index itsl i in

      let itsli = its_prefix itsl i in  
      (* verifier thread state of tid after itsli *)
      let vsi = verifier_thread_state itsli tid in

      let itsli' = its_prefix itsl (i + 1) in
      let vsi' = verifier_thread_state itsli' tid in    
      lemma_verifier_thread_state_extend itsli';  
      assert(vsi' == t_verify_step vsi e);    

      (* the thread store of tid contains k *)
      assert(store_contains (thread_store vsi) k);

      lemma_ext_evict_val_is_stored_val itsl i;      
      assert(v' = stored_value (thread_store vsi) k);

      (* the tid of the last add to k prior to i *)
      let ltid = last_add_tid itsli k in      

      (* the store of ltid contains k and the value is v *)
      lemma_eac_state_instore itsli k;      
      assert(v = stored_value (thread_store (verifier_thread_state itsli ltid)) k);
      
      if ltid = tid then
        (* since both v' and v are equal to stored value, v = v' => a contradiction *)
        hash_collision_contra()
      else (
        (* we know that k is not in any store other than the last add store *)
        lemma_eac_state_instore2 itsli k tid;

        (* k is not in store of tid, a contradiction *)
        hash_collision_contra()
      )
    )

let lemma_non_eac_instore_evictb (#p:pos)   
  (itsl: non_eac_ts_log p{
    EACInStore? (last_valid_eac_state itsl)  /\
    EvictB? (to_vlog_entry (invalidating_log_entry itsl))
   })
  : hash_collision_gen = 
  let st = last_valid_eac_state itsl in   
  let ee = invalidating_log_entry itsl in
  assert(eac_add ee st = EACFail);
  match st with
  | EACInStore m v -> (
    match ee with
    | EvictBlum (EvictB k t) v' tid' ->     
      assert(DVal? v && v' <> v || m <> BAdd);          

      let tsle = time_seq_ext itsl in
      let i = max_eac_prefix tsle in
      let (e,tid) = index itsl i in

      let itsli = its_prefix itsl i in  
      (* verifier thread state of tid after itsli *)
      let vsi = verifier_thread_state itsli tid in

      let itsli' = its_prefix itsl (i + 1) in
      let vsi' = verifier_thread_state itsli' tid in    
      lemma_verifier_thread_state_extend itsli';  
      assert(vsi' == t_verify_step vsi e);    

      (* the thread store of tid contains k *)
      assert(store_contains (thread_store vsi) k);

      let lidx = last_add_idx itsli k in
      let ltid = last_add_tid itsli k in
      let li = project_seq itsli in

      lemma_eac_state_instore_addm itsli k;
      assert(addm_of_entry (index li lidx) = m);
      assert(add_method_of (thread_store vsi) k = BAdd);

      if ltid = tid then (
        assert(add_method_of (thread_store vsi) k = m);
        assert(m = BAdd);
        assert(DVal? v && v' <> v);
        lemma_eac_state_instore itsli k;
        assert(stored_value (thread_store vsi) k = v);

        lemma_ext_evict_val_is_stored_val itsl i;      
        assert(v' = stored_value (thread_store vsi) k);

        hash_collision_contra()
      )
      else (
        (* only the store of last add contains the key k *)
        lemma_eac_state_instore2 itsli k tid;
        assert(not (store_contains (thread_store vsi) k));

        (* ... which is a contradiction *)
        hash_collision_contra()
      )
  )

let lemma_non_eac_instore_evictbm (#p:pos)   
  (itsl: non_eac_ts_log p{
    EACInStore? (last_valid_eac_state itsl)  /\
    EvictBM? (to_vlog_entry (invalidating_log_entry itsl))
   })
  : hash_collision_gen = 
  let st = last_valid_eac_state itsl in   
  let ee = invalidating_log_entry itsl in
  assert(eac_add ee st = EACFail);
  match st with
  | EACInStore m v -> (
    match ee with
    | EvictBlum (EvictBM k k' t) v' tid' ->     
      assert(DVal? v && v' <> v || m <> MAdd);        
      let tsle = time_seq_ext itsl in
      let i = max_eac_prefix tsle in
      let (e,tid) = index itsl i in

      let itsli = its_prefix itsl i in  
      (* verifier thread state of tid after itsli *)
      let vsi = verifier_thread_state itsli tid in

      let itsli' = its_prefix itsl (i + 1) in
      let vsi' = verifier_thread_state itsli' tid in    
      lemma_verifier_thread_state_extend itsli';  
      assert(vsi' == t_verify_step vsi e);    
      
      (* the thread store of tid contains k *)
      assert(store_contains (thread_store vsi) k);

      let lidx = last_add_idx itsli k in
      let ltid = last_add_tid itsli k in
      let li = project_seq itsli in

      lemma_eac_state_instore_addm itsli k;
      assert(addm_of_entry (index li lidx) = m);
      assert(add_method_of (thread_store vsi) k = MAdd);

      if ltid = tid then (
        assert(add_method_of (thread_store vsi) k = m);
        assert(m = MAdd);
        assert(DVal? v && v' <> v);
        lemma_eac_state_instore itsli k;
        assert(stored_value (thread_store vsi) k = v);

        lemma_ext_evict_val_is_stored_val itsl i;      
        assert(v' = stored_value (thread_store vsi) k);

        hash_collision_contra()
      )
      else (    
        (* only the store of last add contains the key k *)
        lemma_eac_state_instore2 itsli k tid;
        assert(not (store_contains (thread_store vsi) k));

        (* ... which is a contradiction *)
        hash_collision_contra()
      )
 )


let lemma_non_eac_evicted_requires_key_in_store (#p:pos)   
  (itsl: non_eac_ts_log p{
    EC.is_eac_state_evicted (last_valid_eac_state itsl)  /\
    requires_key_in_store (to_vlog_entry (invalidating_log_entry itsl))
   })
  : hash_collision_gen = 
  let st = last_valid_eac_state itsl in   
  let ee = invalidating_log_entry itsl in
  assert(eac_add ee st = EACFail);  

  let tsle = time_seq_ext itsl in
  let i = max_eac_prefix tsle in
  let (e,tid) = index itsl i in
  let k = vlog_entry_key e in
  let itsli = its_prefix itsl i in  
  (* verifier thread state of tid after itsli *)
  let vsi = verifier_thread_state itsli tid in

  let itsli' = its_prefix itsl (i + 1) in
  let vsi' = verifier_thread_state itsli' tid in    
  lemma_verifier_thread_state_extend itsli';  
  assert(vsi' == t_verify_step vsi e);    
  
  assert(store_contains (thread_store vsi) k);
  lemma_eac_state_evicted_store itsli k tid;
  hash_collision_contra()

let lemma_non_eac_evicted_merkle_addm (#p:pos)   
  (itsl: non_eac_ts_log p{
    EACEvictedMerkle? (last_valid_eac_state itsl)  /\
    AddM? (to_vlog_entry (invalidating_log_entry itsl))
   })
  : hash_collision_gen = 
  let st = last_valid_eac_state itsl in   
  let ee = invalidating_log_entry itsl in
  assert(eac_add ee st = EACFail);  
  match st with
  | EACEvictedMerkle v_e -> (
    match ee with
    | NEvict (AddM (k,v) k') ->
      assert(v_e <> v);
      let tsle = time_seq_ext itsl in
      let i = max_eac_prefix tsle in
      let (e,tid) = index itsl i in

      let itsli = its_prefix itsl i in  
      (* verifier thread state of tid after itsli *)
      let vsi = verifier_thread_state itsli tid in

      let itsli' = its_prefix itsl (i + 1) in
      let vsi' = verifier_thread_state itsli' tid in    
      lemma_verifier_thread_state_extend itsli';  
      assert(vsi' == t_verify_step vsi e);    

      (* k' is a proper ancestor, so k cannot be root *)
      assert(k <> Root);

      (* k' is the proving ancestor of k *)
      lemma_addm_ancestor_is_proving itsli';
      assert(k' = proving_ancestor itsli k);

      (* k' points to k *)
      lemma_proving_ancestor_points_to_self itsli k;
      lemma_eac_value_is_stored_value itsli k' tid;
      let mv' = to_merkle_value (stored_value (thread_store vsi) k') in
      let d = desc_dir k k' in
      let dh = desc_hash_dir mv' d in
      assert(Desc?.k dh = k);

      (* verifier checks for addm *)
      assert(Desc?.h dh = hashfn v);

      assert(is_eac_state_evicted_merkle itsli k);
      lemma_proving_ancestor_has_hash itsli k;
      lemma_eac_value_is_evicted_value itsli k;
      assert(Desc?.h dh = hashfn v_e);

      (* which gives us a hash collision *)
      SingleHashCollision (Collision v v_e)     
    )

let lemma_non_eac_evicted_blum_addm (#p:pos)   
  (itsl: non_eac_ts_log p{
    EACEvictedBlum? (last_valid_eac_state itsl)  /\
    AddM? (to_vlog_entry (invalidating_log_entry itsl))
   })
  : hash_collision_gen = 
  let st = last_valid_eac_state itsl in   
  let ee = invalidating_log_entry itsl in
  assert(eac_add ee st = EACFail);  
  match st with
  | EACEvictedBlum v_e _ _ -> (
    match ee with
    | NEvict (AddM (k,v) k') ->
      let tsle = time_seq_ext itsl in
      let i = max_eac_prefix tsle in
      let (e,tid) = index itsl i in

      let itsli = its_prefix itsl i in  
      (* verifier thread state of tid after itsli *)
      let vsi = verifier_thread_state itsli tid in

      let itsli' = its_prefix itsl (i + 1) in
      let vsi' = verifier_thread_state itsli' tid in    
      lemma_verifier_thread_state_extend itsli';  
      assert(vsi' == t_verify_step vsi e);    

      (* k' is a proper ancestor, so k cannot be root *)
      assert(k <> Root);

      (* k' is the proving ancestor of k *)
      lemma_addm_ancestor_is_proving itsli';
      assert(k' = proving_ancestor itsli k);

      (* k' points to k *)
      lemma_proving_ancestor_points_to_self itsli k;
      lemma_eac_value_is_stored_value itsli k' tid;      
      let mv' = to_merkle_value (stored_value (thread_store vsi) k') in
      let d = desc_dir k k' in
      let dh = desc_hash_dir mv' d in
      assert(Desc?.k dh = k);
      assert(Desc?.b dh = false);
      
      (* since m = BAdd, this bit should be set to true, a contradiction *)
      lemma_proving_ancestor_blum_bit itsli k;
      hash_collision_contra()      
  )

let lemma_non_eac_evicted_merkle_addb (#p:pos)   
  (itsl: non_eac_ts_log p{
    g_hash_verifiable (partition_idx_seq itsl) /\  
    EACEvictedMerkle? (last_valid_eac_state itsl)  /\
    AddB? (to_vlog_entry (invalidating_log_entry itsl))
   })
  : hash_collision_gen = 
  (* hash verifiable - evict hash and add hash equal *)                          
  let gl = partition_idx_seq itsl in                           
  assert(g_hadd gl = g_hevict gl);
  
  let st = last_valid_eac_state itsl in   
  let ee = invalidating_log_entry itsl in
  assert(eac_add ee st = EACFail);  
  match st with
  | EACEvictedMerkle v_e -> (
    match ee with
    | NEvict (AddB (k,v) t j) ->
      let tsle = time_seq_ext itsl in
      let i = max_eac_prefix tsle in
      let (e,tid) = index itsl i in

      let itsli = its_prefix itsl i in  
      (* verifier thread state of tid after itsli *)
      let vsi = verifier_thread_state itsli tid in

      let itsli' = its_prefix itsl (i + 1) in
      let vsi' = verifier_thread_state itsli' tid in    
      lemma_verifier_thread_state_extend itsli';  
      assert(vsi' == t_verify_step vsi e);    

      (* number of blum evicts is the same as blum adds in the first i entries *)
      lemma_evict_add_count_same_evictedm itsli k;
      assert(MS.size (ts_add_set_key itsli k) = MS.size (ts_evict_set_key itsli k));

      (* the ith element is a blum add *)
      assert(is_blum_add #p (e,tid));
      lemma_ts_add_set_key_extend itsli';
      assert(ts_add_set_key itsli' k == add_elem (ts_add_set_key itsli k)
                                                 (blum_add_elem #p (e,tid)));

      (* the ith element is not a blum evict *)
      assert(not (is_blum_evict (index itsl i)));
      lemma_ts_evict_set_key_extend2 itsli';
      assert(ts_evict_set_key itsli' k == ts_evict_set_key itsli k);

      (* this implies that the size of the add set after processing (i+1) elements 
         * is one larger than the evict set at this point *)
      assert(MS.size (ts_add_set_key itsli' k) = 1 + (MS.size (ts_evict_set_key itsli' k)));

      (* this implies that in the first (i+1) entries there is an element whose membership in 
         * add multiset is > its membership in evict multiset *)
      let be = diff_elem (ts_add_set_key itsli' k) (ts_evict_set_key itsli' k) in
      lemma_ts_add_set_key_contains_only itsli' k be;
      assert(MH.key_of be = k);

      lemma_mem_key_add_set_same itsli' be;
      lemma_mem_key_evict_set_same itsli' be;  
      assert(MS.mem be (ts_add_set itsli') > MS.mem be (ts_evict_set itsli'));

      (* the index of be in the add set *)
      let i_be = some_add_elem_idx itsli' be in
      assert(i_be <= i);

      (* from clock orderedness any evict_set entry for be should happen before i *)
      lemma_evict_before_add2 itsl i_be;
      assert(MS.mem be (ts_evict_set itsl) = MS.mem be (ts_evict_set (its_prefix itsl i_be)));

      (* any set membership is monotonic *)
      lemma_mem_monotonic be itsl (i + 1);
      lemma_mem_monotonic be itsli' i_be;
      assert(MS.mem be (ts_add_set itsl) >= MS.mem be (ts_add_set itsli'));
      assert(MS.mem be (ts_evict_set itsl) = MS.mem be (ts_evict_set itsli'));

      (* this implies the membership of be in (overall) addset > membership in evict set *)
      (* so these two sets are not equal providing a hash collision *)
      assert(MS.mem be (ts_add_set itsl) > MS.mem be (ts_evict_set itsl));  

      MS.lemma_not_equal (ts_add_set itsl) (ts_evict_set itsl) be;
      assert(~( (ts_add_set itsl) == (ts_evict_set itsl)));

      lemma_ts_add_set_correct itsl;
      lemma_ts_evict_set_correct itsl;
      assert(~ (g_add_set gl == g_evict_set gl));

      lemma_g_hadd_correct gl;
      lemma_ghevict_correct gl;

      MultiHashCollision (MSCollision (g_add_seq gl) (g_evict_seq gl))
  )

let lemma_non_eac_evicted_blum_addb (#p:pos)   
  (itsl: non_eac_ts_log p{
    g_hash_verifiable (partition_idx_seq itsl) /\  
    EACEvictedBlum? (last_valid_eac_state itsl)  /\
    AddB? (to_vlog_entry (invalidating_log_entry itsl))
   })
  : hash_collision_gen = 
  (* hash verifiable - evict hash and add hash equal *)                          
  let gl = partition_idx_seq itsl in                           

  let st = last_valid_eac_state itsl in   
  let ee = invalidating_log_entry itsl in
  match st with
  | EACEvictedBlum v_e t j -> (
    match ee with
    | NEvict (AddB (k, v) t' j') ->
    //assert(v_e <> v || t' <> t || j' <> j);

    let tsle = time_seq_ext itsl in
    let i = max_eac_prefix tsle in
    let (e,tid) = index itsl i in

    let itsli = its_prefix itsl i in  
    (* verifier thread state of tid after itsli *)
    let vsi = verifier_thread_state itsli tid in

    let itsli' = its_prefix itsl (i + 1) in
    let vsi' = verifier_thread_state itsli' tid in    
    lemma_verifier_thread_state_extend itsli';  
    //assert(vsi' == t_verify_step vsi e);    

    let be = blum_add_elem (index itsl i) in

    (* the previous operation of k is a blum evict *)
    lemma_eac_evicted_blum_implies_previous_evict itsli k;
    let i' = last_idx_of_key itsli k in
    //assert(is_blum_evict (index itsli i'));

    (* since EAC failed, the blum element added to evict set at i' <> blum element added to 
     * add set at i *)
    let be' = blum_evict_elem itsli i' in
    //assert(be <> be');

    if MS.contains be (ts_evict_set itsl) then (

      (* since evict set is a set we can identify the unique index that produces be *)
      let j = index_blum_evict itsl be in
      //assert(is_blum_evict (index itsl j));
      //assert(blum_evict_elem itsl j = be);

      (* from clock ordering j has to occur before i *)
      lemma_evict_before_add3 itsl i j;
      //assert (j < i);
      
      //assert(entry_of_key k (index itsli j));
      lemma_last_index_correct2 (entry_of_key k) itsli j;

      //lemma_index_blum_evict_prefix itsl i i';
      //assert(be' = blum_evict_elem itsli i');
      //assert(blum_evict_elem itsl i' = blum_evict_elem itsli i');
      //assert(j < i');
      //assert(be' = blum_evict_elem itsl i');

      lemma_evict_has_next_add itsli j;
      lemma_blum_evict_add_same itsli j;

      let j' = next_add_of_key itsli j k in
      //assert(blum_add_elem (index itsli j') = be);
      //assert(j' <> i);
      lemma_add_set_mem itsl i j';
      //assert(MS.mem be (ts_add_set itsl) >= 2);

      lemma_ts_add_set_correct itsl;
      //assert(MS.mem be (g_add_set gl) >= 2);
      g_evict_set_is_set gl;
      //assert(is_set (g_evict_set gl));
      //assert(MS.mem be (g_evict_set gl) <= 1);
      MS.lemma_not_equal (g_add_set gl) (g_evict_set gl) be;

      lemma_ghevict_correct gl;
      lemma_g_hadd_correct gl;

      MultiHashCollision (MSCollision (g_add_seq gl) (g_evict_seq gl))      
    )
    else (
      
      lemma_ts_add_set_contains_add_elem itsl i;
      //assert(MS.contains be (ts_add_set itsl));

      MS.lemma_not_equal (ts_add_set itsl) (ts_evict_set itsl) be;     
      lemma_ts_evict_set_correct itsl;
      lemma_ts_add_set_correct itsl;     
      //assert(~ (g_add_set gl == g_evict_set gl));

      lemma_ghevict_correct gl;
      lemma_g_hadd_correct gl;

      MultiHashCollision (MSCollision (g_add_seq gl) (g_evict_seq gl))      
    )
 )

let lemma_non_eac_time_seq_implies_hash_collision 
  (#n:pos) 
  (itsl: non_eac_ts_log n{g_hash_verifiable (partition_idx_seq itsl)}): hash_collision_gen = 
  
  let st = last_valid_eac_state itsl in
  let ee = invalidating_log_entry itsl in
  let tsle = time_seq_ext itsl in  
  let i = max_eac_prefix tsle in
  
  match st with
  | EACInit -> (
      match ee with 
      | NEvict (Get _ _) -> lemma_non_eac_init_requires_key_in_store itsl
      | NEvict (Put _ _) -> lemma_non_eac_init_requires_key_in_store itsl
      | NEvict (AddB _ _ _) -> lemma_non_eac_init_addb itsl
      | NEvict (AddM (k,v) _) -> lemma_non_eac_init_addm itsl
      | EvictMerkle (EvictM _ _) _ -> lemma_non_eac_init_evict itsl
      | EvictBlum (EvictB _ _) _ _ -> lemma_non_eac_init_evict itsl
      | EvictBlum (EvictBM _ _ _) _ _ -> lemma_non_eac_init_evict itsl
    )
  | EACInStore m v -> (
    match ee with 
      | NEvict (Get _ _) -> lemma_non_eac_instore_get itsl
      | NEvict (Put _ _) -> lemma_non_eac_instore_put itsl
      | NEvict (AddB _ _ _) -> lemma_non_eac_instore_addb itsl
      | NEvict (AddM (k,v) _) -> lemma_non_eac_instore_addm itsl
      | EvictMerkle (EvictM _ _) _ -> lemma_non_eac_instore_evictm itsl
      | EvictBlum (EvictB _ _) _ _ -> lemma_non_eac_instore_evictb itsl
      | EvictBlum (EvictBM _ _ _) _ _ -> lemma_non_eac_instore_evictbm itsl
  )
  | EACEvictedMerkle v -> (
    match ee with 
      | NEvict (Get _ _) -> lemma_non_eac_evicted_requires_key_in_store itsl
      | NEvict (Put _ _) -> lemma_non_eac_evicted_requires_key_in_store itsl
      | NEvict (AddB _ _ _) ->  lemma_non_eac_evicted_merkle_addb itsl
      | NEvict (AddM (k,v) _) -> lemma_non_eac_evicted_merkle_addm itsl
      | EvictMerkle (EvictM _ _) _ -> lemma_non_eac_evicted_requires_key_in_store itsl
      | EvictBlum (EvictB _ _) _ _ -> lemma_non_eac_evicted_requires_key_in_store itsl
      | EvictBlum (EvictBM _ _ _) _ _ -> lemma_non_eac_evicted_requires_key_in_store itsl
  )
  | EACEvictedBlum v t tid -> (
    match ee with 
      | NEvict (Get _ _) -> lemma_non_eac_evicted_requires_key_in_store itsl
      | NEvict (Put _ _) -> lemma_non_eac_evicted_requires_key_in_store itsl
      | NEvict (AddB _ _ _) ->  lemma_non_eac_evicted_blum_addb itsl
      | NEvict (AddM (k,v) _) -> lemma_non_eac_evicted_blum_addm itsl
      | EvictMerkle (EvictM _ _) _ -> lemma_non_eac_evicted_requires_key_in_store itsl
      | EvictBlum (EvictB _ _) _ _ -> lemma_non_eac_evicted_requires_key_in_store itsl
      | EvictBlum (EvictBM _ _ _) _ _ -> lemma_non_eac_evicted_requires_key_in_store itsl
  )

