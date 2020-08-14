module Veritas.Verifier.EAC

open FStar.Seq
open Veritas.EAC
open Veritas.Hash
open Veritas.Interleave
open Veritas.Key
open Veritas.MultiSetHash
open Veritas.SeqAux
open Veritas.SeqMachine
open Veritas.State
open Veritas.Verifier
open Veritas.Verifier.CorrectDefs

type its_log (n:nat) = 
  s:seq (idx_elem #vlog_entry n){g_verifiable (partition_idx_seq s) /\
                                 g_hash_verifiable (partition_idx_seq s)}

(* generalized single- and multi-set hash collision *)
type hash_collision_gen =
  | SingleHashCollision: hc: hash_collision -> hash_collision_gen
  | MultiHashCollision: hc: ms_hash_collision -> hash_collision_gen

(* extended time sequence log (with evict values) *)
let time_seq_ext (#n:nat) (itsl: its_log n): (le:vlog_ext{project_seq itsl = to_vlog le}) =
  admit()

type eac_ts_log (#n:nat) = itsl: its_log n {is_eac_log (time_seq_ext itsl)}
type non_eac_ts_log (#n:nat) = itsl: its_log n {not (is_eac_log (time_seq_ext itsl))}

let eac_invalidating_key (#n:nat) (itsl: non_eac_ts_log #n): key =
  let tsle = time_seq_ext itsl in

  (* maximum eac valid prefix *)
  let i = max_eac_prefix tsle in

  (* ee is the entry causing eac invalidation *)
  let ee = index tsle i in
  
  (* the key causing the invalidation *)
  partn_fn eac_sm ee


let last_valid_eac_state (#n:nat) (itsl: non_eac_ts_log #n): eac_state = 

  let tsle = time_seq_ext itsl in
  
  let i = max_eac_prefix tsle in

  (* maximum eac prefix *)
  let tslei = prefix tsle i in

  (* minimum non-eac prefix *)
  let tslei' = prefix tsle (i + 1) in

  lemma_first_invalid_key eac_sm tsle;

  (* ee is the entry causing eac invalidation *)
  let ee = index tsle i in
  
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

  st

let lemma_non_eac_time_seq_implies_hash_collision (#n:nat) (itsl: non_eac_ts_log #n): hash_collision_gen = 
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
  assert(st = last_valid_eac_state itsl);
  
  lemma_reduce_prefix EACInit eac_add (prefix tslek (j + 1)) j;  
  lemma_reduce_singleton st eac_add (suffix (prefix tslek (j + 1)) 1);
  assert(eac_add ee st = EACFail);
  
  match st with
  | EACInit -> admit()
  | EACInCache m v -> admit()
  | EACEvicted m v -> admit()
