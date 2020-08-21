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
open Veritas.Verifier.TSLog

module MS = Veritas.MultiSet
module MH = Veritas.MultiSetHash

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
  Lemma (EACFail <> last_valid_eac_state itsl /\
         EACFail = eac_add (invalidating_log_entry itsl) (last_valid_eac_state itsl)) =            
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

let its_vlog_entry (#n:pos) (itsl: its_log n) (i:seq_index itsl): vlog_entry =
  fst (index itsl i)

let its_thread_id (#n:pos) (itsl: its_log n) (i:seq_index itsl): (tid:nat{tid < n}) =
  snd (index itsl i)

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
  lemma_unzip_index itsl i

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
                           is_evict (to_vlog_entry (invalidating_log_entry itsl))}): hash_collision_gen =
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

let lemma_non_eac_time_seq_implies_hash_collision 
  (#n:pos) 
  (itsl: non_eac_ts_log n{g_hash_verifiable (partition_idx_seq itsl)}): hash_collision_gen = 
  let st = last_valid_eac_state itsl in
  let ee = invalidating_log_entry itsl in
  match st with
  | EACInit -> (
      match ee with 
      | NEvict (Get _ _) -> lemma_non_eac_init_requires_key_in_store itsl
      | NEvict (Put _ _) -> lemma_non_eac_init_requires_key_in_store itsl
      | NEvict (AddB _ _ _) -> lemma_non_eac_init_addb itsl
      | Evict (EvictM _ _) _ -> lemma_non_eac_init_evict itsl
      | _ -> admit()
    )
  | EACInStore m v -> admit()
  | EACEvicted m v -> admit()
