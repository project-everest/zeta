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
  Lemma (time_seq_ext (its_prefix itsl i) = prefix (time_seq_ext itsl) i) = 
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
let lemma_eac_state_init_store (#n:nat) (itsl: its_log n) (k: key{k <> Root}) (id:nat{id < n}):
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
  vlog_entry_key (invalidating_log_entry itsl)

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
  lemma_filter_prefix_comm (iskey vlog_entry_key k) tsle i;
  assert(st = last_valid_eac_state itsl);

  lemma_reduce_prefix EACInit eac_add (prefix tslek (j + 1)) j;  
  lemma_reduce_singleton st eac_add (suffix (prefix tslek (j + 1)) 1);
  assert(eac_add ee st = EACFail);

  ()         

(* eac invalidation is caused by a get as the first operation *)
let lemma_non_eac_init_get (#n:nat) 
  (itsl: non_eac_ts_log #n{last_valid_eac_state itsl = EACInit /\
                           Get? (to_vlog_entry (invalidating_log_entry itsl))}): hash_collision_gen = 
  let tsle = time_seq_ext itsl in  
  let i = max_eac_prefix tsle in
  let ee = invalidating_log_entry itsl in
  let e = to_vlog_entry ee in
  let k = vlog_entry_key ee in
  let st = last_valid_eac_state itsl in
  assert(st = EACInit);
  assert(is_data_key k);
  assert(length tsle = length itsl);
  let itsli = its_prefix itsl i in
  let tslei = time_seq_ext itsli in
  lemma_its_prefix_ext itsl i;
  assert(tslei = prefix tsle i);

  assert(eac_state_key tslei k = st);
  let (_,id) = index itsl i in
  assert(id < n);  
  lemma_eac_state_init_store itsli k id;

  let gli = partition_idx_seq itsli in
  let igli = attach_index gli in
  let tsli_id = verifier_thread_state itsli id in
  assert(not (store_contains (thread_store tsli_id) k));

  let itsli' = its_prefix itsl (i + 1) in
  let gli' = partition_idx_seq itsli' in
  let tsli'_id = verifier_thread_state itsli' id in 
  assert(Valid? tsli'_id);

  lemma_partition_idx_extend1 itsli';
  assert(index gli' id = append1 (index gli id) (fst (telem itsli')));
  assert(telem itsli' = index itsl i);
  let ec = fst (index itsl i) in
  let tslei' = time_seq_ext itsli' in

  admit()

let lemma_non_eac_time_seq_implies_hash_collision (#n:nat) (itsl: non_eac_ts_log #n): hash_collision_gen = 
  let st = last_valid_eac_state itsl in
  let ee = invalidating_log_entry itsl in
  match st with
  | EACInit -> (
      match ee with 
      | NEvict (Get _ _) -> lemma_non_eac_init_get itsl            
      | _ -> admit()
    )
  | EACInCache m v -> admit()
  | EACEvicted m v -> admit()
