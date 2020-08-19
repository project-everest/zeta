module Veritas.Verifier.EAC

open FStar.Seq
open Veritas.BinTree
open Veritas.EAC
open Veritas.Hash
open Veritas.Interleave
open Veritas.Key
open Veritas.MultiSetHash
open Veritas.Record
open Veritas.SeqAux
open Veritas.SeqMachine
open Veritas.State
open Veritas.Verifier
open Veritas.Verifier.CorrectDefs

(* generalized single- and multi-set hash collision *)
type hash_collision_gen =
  | SingleHashCollision: hc: hash_collision -> hash_collision_gen
  | MultiHashCollision: hc: ms_hash_collision -> hash_collision_gen

(* construct a hash collision from a contradiction *)
let hash_collision_contra (_:unit{False}): hash_collision_gen = 
  SingleHashCollision (Collision (DVal Null) (DVal Null))

(* the eac state of a key after processing an eac_log *)
let eac_state_key (le: vlog_ext) (k:key): eac_state = 
  let lek = partn eac_sm k le in
  seq_machine_run eac_smk lek

(* the eac state of a key at the end of an its log *)
let eac_state_of_key (#n:nat) (itsl: its_log n) (k:key): eac_state = 
  let tsle = time_seq_ext itsl in 
  let tslek = partn eac_sm k tsle in
  seq_machine_run eac_smk tslek

(* is the eac state of key at the end of its_log init *)
let is_eac_state_init (#n:nat) (itsl: its_log n) (k:key): bool =
  eac_state_of_key itsl k = EACInit

(* is the key k in evicted state in *)
let is_eac_state_evicted (#n:nat) (itsl: its_log n) (k:key): bool = 
  EACEvicted? (eac_state_of_key itsl k)

(* is the key k in instore state after processing its_log *)
let is_eac_state_instore (#n:nat) (itsl: its_log n) (k:key):bool = 
  EACInStore? (eac_state_of_key itsl k)

(* the state of a verifier thread after processing entries in a log *)
let verifier_thread_state (#n:nat) (itsl: its_log n) (id:nat{id < n}): (st:vtls{Valid? st}) = 
  let gl = partition_idx_seq itsl in
  assert(t_verifiable (index (attach_index gl) id));
  t_verify id (index gl id)

(* 
 * when the eac state of a key is Init (no operations on the key yet) no 
 * thread contains the key in its store 
 *)
let lemma_eac_state_init_store 
   (#n:nat) 
   (itsl: eac_ts_log n) (k: key{k <> Root && is_eac_state_init itsl k}) (id:nat{id < n}):
   Lemma (not (store_contains (thread_store (verifier_thread_state itsl id)) k)) 
   = admit()

(* when the eac state of a key is EACEvicted then no thread contains the key in its store *)
let lemma_eac_state_evicted_store (#n:nat) (itsl: eac_ts_log n) 
  (k: key{is_eac_state_evicted itsl k}) (id:nat{id < n}):
    Lemma (not (store_contains (thread_store (verifier_thread_state itsl id)) k)) = admit()

(* does a log have some add entry *)
let has_some_add (l:seq vlog_entry): bool = 
  exists_sat_elems is_add l

(* does a log have some add of key k *)
let has_some_add_of_key (k:key) (l:seq vlog_entry): bool = 
  exists_sat_elems (is_add_of_key k) l 
  
(* when the eac state of a key is "instore" then there is always a previous add *)
let lemma_eac_state_instore_implies_prev_add (#n:nat) (itsl: eac_ts_log n) (k:key{is_eac_state_instore itsl k}):
  Lemma (has_some_add_of_key k (project_seq itsl)) = admit()

(* when the eac state of a key is instore return the index of the last add that transitioned
 * the key k to "instore" *)
let last_add_idx (#n:nat) (itsl: eac_ts_log n) (k: key{is_eac_state_instore itsl k}): seq_index itsl =
   lemma_eac_state_instore_implies_prev_add itsl k;
   last_index (is_add_of_key k) (project_seq itsl)

(* the verifier thread where the last add of key k happens *)
let last_add_tid (#n:nat) (itsl: eac_ts_log n) (k: key{is_eac_state_instore itsl k}): (tid:nat{tid < n}) =
  snd (index itsl (last_add_idx itsl k))

(* if the eac_state of k is instore, then that k is in the store of the verifier thread of its last add *)
let lemma_eac_state_instore (#n:nat) (itsl: eac_ts_log n) (k:key{is_eac_state_instore itsl k}):
  Lemma (store_contains (thread_store (verifier_thread_state itsl (last_add_tid itsl k))) k) = admit()

(* the entry that causes the eac_invalidation *)
let invalidating_log_entry (#n:nat) (itsl: non_eac_ts_log n): vlog_entry_ext = 
  let tsle = time_seq_ext itsl in  
  let i = max_eac_prefix tsle in  
  index tsle i

(* the key that causes the eac_invalidation *)
let eac_invalidating_key (#n:nat) (itsl: non_eac_ts_log n): key =
  vlog_entry_ext_key (invalidating_log_entry itsl)

(* last valid eac state *)
let last_valid_eac_state (#n:nat) (itsl: non_eac_ts_log n): eac_state = 
  let tsle = time_seq_ext itsl in  
  let i = max_eac_prefix tsle in
  let k = eac_invalidating_key itsl in
  eac_state_key (prefix tsle i) k
  
(* applying the invalidating entry on the last valid state produces EAC failure *)
let lemma_invalidation (#n:nat) (itsl: non_eac_ts_log n):
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

let its_vlog_entry (#n:nat) (itsl: its_log n) (i:seq_index itsl): vlog_entry =
  fst (index itsl i)

let its_thread_id (#n:nat) (itsl: its_log n) (i:seq_index itsl): (tid:nat{tid < n}) =
  snd (index itsl i)

let lemma_verifier_thread_state_extend (#n:nat) (itsl: its_log n{length itsl > 0}):
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

let lemma_time_seq_ext_correct (#n:nat) (itsl: its_log n) (i:seq_index itsl):
  Lemma (requires True)
        (ensures (its_vlog_entry itsl i = to_vlog_entry (index (time_seq_ext itsl) i))) 
        [SMTPat (to_vlog_entry (index (time_seq_ext itsl) i))] =
  lemma_unzip_index itsl i

(* if an operation requires the key in store, it cannot be the first operation *)
let lemma_non_eac_init_requires_key_in_store (#n:nat) 
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
  lemma_verifier_thread_state_extend itsli';
  assert(verifier_thread_state itsli' tid == t_verify_step (verifier_thread_state itsli tid) e);
  
  let k = vlog_entry_key e in
  lemma_eac_state_init_store itsli k tid;
  hash_collision_contra ()

(* the first operation for a key cannot be evict *)
let lemma_non_eac_init_evict (#n:nat)
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
  assert(verifier_thread_state itsli' tid == t_verify_step (verifier_thread_state itsli tid) e);

  let k = vlog_entry_key e in
  lemma_root_never_evicted (verifier_thread_state itsli tid) e;  
  assert(k <> Root);                               
  lemma_non_eac_init_requires_key_in_store itsl

(* the first operation for a key cannot be a blum add *)
let lemma_non_eac_init_addb (#n)
  (itsl: non_eac_ts_log n{last_valid_eac_state itsl = EACInit /\
                           AddB? (to_vlog_entry (invalidating_log_entry itsl))}): hash_collision_gen =
  admit()                           

let lemma_non_eac_time_seq_implies_hash_collision (#n:nat) (itsl: non_eac_ts_log n): hash_collision_gen = 
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
