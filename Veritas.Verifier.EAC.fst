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

type its_log (n:nat) = 
  s:seq (idx_elem #vlog_entry n){g_verifiable (partition_idx_seq s)}

(* extended time sequence log (with evict values) *)
let time_seq_ext (#n:nat) (itsl: its_log n): (le:vlog_ext{project_seq itsl = to_vlog le}) =
  admit()

(* the prefix of an its log *)
let its_prefix (#n:nat) (itsl: its_log n) (i:nat{i <= length itsl}): 
  (itsl':its_log n{length itsl' = i}) =
  let itsl': seq (idx_elem #vlog_entry n) = prefix itsl i in
  let gl = partition_idx_seq itsl in
  let idgl = g_tid_vlog gl in
  
  let gl' = partition_idx_seq itsl' in
  let idgl' = g_tid_vlog gl' in

  let aux (id:nat{id < n}):
    Lemma (requires True)
          (ensures (t_verifiable (index idgl' id)))
          [SMTPat (t_verifiable (index idgl' id))]    
    = 
    let (_,l') = index idgl' id in
    //let (_,l) = index idgl id in    
    lemma_partition_idx_prefix_comm itsl i  id;
    lemma_verifiable_implies_prefix_verifiable (index idgl id) (length l');
    ()
  in
  itsl'

let lemma_its_prefix_ext (#n:nat) (itsl:its_log n) (i:nat{i <= length itsl}):
  Lemma (requires True)
        (ensures (time_seq_ext (its_prefix itsl i) = prefix (time_seq_ext itsl) i))
        [SMTPat (time_seq_ext (its_prefix itsl i))] = 
  admit()

(* the eac state of a key after processing an eac_log *)
let eac_state_key (le: vlog_ext) (k:key): eac_state = 
  let lek = partn eac_sm k le in
  seq_machine_run eac_smk lek

(* the state of a verifier thread after processing entries in a log *)
let verifier_thread_state (#n:nat) (itsl: its_log n) (id:nat{id < n}): (st:vtls{Valid? st}) = 
  let gl = partition_idx_seq itsl in
  assert(t_verifiable (index (attach_index gl) id));
  t_verify id (index gl id)

(* generalized single- and multi-set hash collision *)
type hash_collision_gen =
  | SingleHashCollision: hc: hash_collision -> hash_collision_gen
  | MultiHashCollision: hc: ms_hash_collision -> hash_collision_gen

(* construct a hash collision from a contradiction *)
let hash_collision_contra (_:unit{False}): hash_collision_gen = 
  SingleHashCollision (Collision (DVal Null) (DVal Null))

(* 
 * when the eac state of a key is Init (no operations on the key yet) no 
 * thread contains the key in its store 
 *)
let lemma_eac_state_init_store 
   (#n:nat) 
   (itsl: its_log n) (k: key{k <> Root /\ 
                             EACInit = eac_state_key (time_seq_ext itsl) k}) (id:nat{id < n}):
   Lemma (not (store_contains (thread_store (verifier_thread_state itsl id)) k)) 
   = admit()

type eac_ts_log (#n:nat) = itsl: its_log n {is_eac_log (time_seq_ext itsl)}
type non_eac_ts_log (#n:nat) = itsl: its_log n {not (is_eac_log (time_seq_ext itsl))}

(* the entry that causes the eac_invalidation *)
let invalidating_log_entry (#n:nat) (itsl: non_eac_ts_log #n): vlog_entry_ext = 
  let tsle = time_seq_ext itsl in  
  let i = max_eac_prefix tsle in  
  index tsle i

(* the key that causes the eac_invalidation *)
let eac_invalidating_key (#n:nat) (itsl: non_eac_ts_log #n): key =
  vlog_entry_ext_key (invalidating_log_entry itsl)

(* last valid eac state *)
let last_valid_eac_state (#n:nat) (itsl: non_eac_ts_log #n): eac_state = 
  let tsle = time_seq_ext itsl in  
  let i = max_eac_prefix tsle in
  let k = eac_invalidating_key itsl in
  eac_state_key (prefix tsle i) k
  
(* applying the invalidating entry on the last valid state produces EAC failure *)
let lemma_invalidation (#n:nat) (itsl: non_eac_ts_log #n):
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

(* if an operation requires the key in cache, it cannot be the first operation *)
let lemma_non_eac_init_requires_key_in_cache (#n:nat) 
  (itsl: non_eac_ts_log #n{last_valid_eac_state itsl = EACInit /\
                           requires_key_in_cache (to_vlog_entry (invalidating_log_entry itsl)) /\
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
  (itsl: non_eac_ts_log #n{last_valid_eac_state itsl = EACInit /\
                           requires_key_in_cache (to_vlog_entry (invalidating_log_entry itsl)) /\
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
  lemma_non_eac_init_requires_key_in_cache itsl

(* the first operation for a key cannot be a blum add *)
let lemma_non_eac_init_addb (#n)
  (itsl: non_eac_ts_log #n{last_valid_eac_state itsl = EACInit /\
                           AddB? (to_vlog_entry (invalidating_log_entry itsl))}): hash_collision_gen =
  admit()                           

let lemma_non_eac_time_seq_implies_hash_collision (#n:nat) (itsl: non_eac_ts_log #n): hash_collision_gen = 
  let st = last_valid_eac_state itsl in
  let ee = invalidating_log_entry itsl in
  match st with
  | EACInit -> (
      match ee with 
      | NEvict (Get _ _) -> lemma_non_eac_init_requires_key_in_cache itsl
      | NEvict (Put _ _) -> lemma_non_eac_init_requires_key_in_cache itsl
      | NEvict (AddB _ _ _) -> lemma_non_eac_init_addb itsl
      | Evict (EvictM _ _) _ -> lemma_non_eac_init_evict itsl
      | _ -> admit()
    )
  | EACInCache m v -> admit()
  | EACEvicted m v -> admit()
