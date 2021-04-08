module Veritas.Intermediate.Logs

open FStar.Seq
open Veritas.BinTree
open Veritas.Key
open Veritas.MultiSetHashDomain
open Veritas.Record
open Veritas.SeqAux
open Veritas.State

open Veritas.Intermediate.VerifierConfig
open Veritas.Intermediate.SlotKeyRel

module Spec = Veritas.Verifier

(* Definitions of different styles of verifier logs.
   - logK : contains only key references (defined in Veritas.Verifier)
   - logS: contains slot references
   - logL: contains slot references & low-level data structures (TODO) *)

let thread_id = Spec.thread_id

let logK_entry = Spec.vlog_entry
let logK = Spec.vlog

type logS_entry (vcfg:verifier_config) =
  | Get_S: s:slot_id vcfg -> k:data_key -> v:data_value -> logS_entry vcfg
  | Put_S: s:slot_id vcfg -> k:data_key -> v:data_value -> logS_entry vcfg
  | AddM_S: s:slot_id vcfg -> r:record -> s':slot_id vcfg -> logS_entry vcfg
  | EvictM_S: s:slot_id vcfg -> s':slot_id vcfg -> logS_entry vcfg
  | AddB_S: s:slot_id vcfg -> r:record -> t:timestamp -> j:thread_id -> logS_entry vcfg
  | EvictB_S: s:slot_id vcfg -> t:timestamp -> logS_entry vcfg
  | EvictBM_S: s:slot_id vcfg -> s':slot_id vcfg -> t:timestamp -> logS_entry vcfg

let logS vcfg = Seq.seq (logS_entry vcfg)

let is_state_op #vcfg (e: logS_entry vcfg): bool =
  match e with
  | Get_S _ _ _ | Put_S _ _ _ -> true
  | _ -> false

let to_state_op #vcfg (e:logS_entry vcfg {is_state_op e}): state_op =
  match e with
  | Get_S _ k v -> Get k v
  | Put_S _ k v -> Put k v

let to_state_ops #vcfg (l: logS vcfg) =
  map to_state_op (filter_refine is_state_op l)

let is_blum_add #vcfg (e: logS_entry vcfg): bool =
  match e with
  | AddB_S _ _ _ _ -> true
  | _ -> false

let is_evict_to_blum #vcfg (e:logS_entry vcfg): bool =
  match e with
  | EvictB_S _ _ -> true
  | EvictBM_S _ _ _ -> true
  | _ -> false

let slot_of #vcfg (e:logS_entry vcfg): slot_id _ =
  match e with
  | Get_S s _ _ -> s
  | Put_S s _ _ -> s
  | AddM_S s _ _ -> s
  | EvictM_S s _ -> s
  | AddB_S s _ _ _ -> s
  | EvictB_S s _ -> s
  | EvictBM_S s _ _ -> s

(*
 * Given a slot -> key mapping, we define a boolean whether a log entry is valid.
 * This definition checks if the slots are used correctly:
 * (a) We add to a slot only if it is free
 * (b) We evict from a slot only if it is associated with a key
 * (c) We reference a slot in Get/Put and as an ancestor in Add/Evict only if it is associated with a key
 *)
let valid_logS_entry #vcfg (ssm: slot_state_map vcfg) (e: logS_entry vcfg): bool =
  match e with
  | Get_S s k _
  | Put_S s k _ ->
    is_assoc_with ssm s k
  | AddM_S s (k,_) s' ->
    is_free ssm s && is_assoc ssm s'
  | AddB_S s (k,_) _ _ ->
    is_free ssm s
  | EvictM_S s s' ->
    is_assoc ssm s && is_assoc ssm s'
  | EvictB_S s _ ->
    is_assoc ssm s
  | EvictBM_S s s' _ ->
    is_assoc ssm s && is_assoc ssm s'

let to_logK_entry #vcfg (ssm: slot_state_map vcfg) (e: logS_entry vcfg{valid_logS_entry ssm e}): logK_entry =
  match e with
  | Get_S s k v -> Spec.Get k v
  | Put_S s k v -> Spec.Put k v
  | AddM_S s r s' -> Spec.AddM r (assoc_key ssm s')
  | AddB_S s r t j -> Spec.AddB r t j
  | EvictM_S s s' -> Spec.EvictM (assoc_key ssm s) (assoc_key ssm s')
  | EvictB_S s t -> Spec.EvictB (assoc_key ssm s) t
  | EvictBM_S s s' t -> Spec.EvictBM (assoc_key ssm s) (assoc_key ssm s') t

(*
 * define a state machine over slot_states; to allow for "failures" where the log
 * uses slot states in an inconsistent manner (e.g., evict a slot without adding to it)
 * we make the transition function return option slot_state, with None being failure.
 *)
let slot_state_trans #vcfg (e:logS_entry vcfg) (s:slot_id vcfg) (sst: slot_state): option slot_state =
  match e with
  | Get_S s1 k1 _
  | Put_S s1 k1 _ ->
    if s = s1 then
      if Assoc? sst && Assoc?.k sst = k1 then Some sst
      else None
    else Some sst
  | AddM_S s1 (k1,_) s2 ->
    if s = s1 then
      if Free? sst then Some (Assoc k1)
      else None
    else if s = s2 then
      if Assoc? sst then Some sst
      else None
    else Some sst
  | AddB_S s1 (k1,_) _ _ ->
    if s = s1 then
      if Free? sst then Some (Assoc k1)
      else None
    else Some sst
  | EvictM_S s1 s2 ->
    if s = s1 then
      if Assoc? sst then Some Free
      else None
    else if s = s2 then
      if Assoc? sst then Some sst
      else None
    else Some sst
  | EvictB_S s1 _ ->
    if s = s1 then
      if Assoc? sst then Some Free
      else None
    else Some sst
  | EvictBM_S s1 s2 _ ->
    if s = s1 then
      if Assoc? sst then Some Free
      else None
    else if s = s2 then
      if Assoc? sst then Some sst
      else None
    else Some sst

let has_distinct_slots #vcfg (e: logS_entry vcfg): bool =
  match e with
  | AddM_S s _ s' -> s <> s'
  | EvictM_S s s' -> s <> s'
  | EvictBM_S s s' _ -> s <> s'
  | _ -> true

let rec slot_state_trans_closure #vcfg (s:slot_id vcfg) (l:logS vcfg) (sst_init: slot_state)
  : Tot (option slot_state) (decreases (length l)) =
  let n = length l in
  if n = 0 then Some (sst_init)
  else
    let l' = hprefix l in
    let e = telem l in
    let osst' = slot_state_trans_closure s l' sst_init in
    if None? osst' then None
    else if not (has_distinct_slots e) then None
    else
      slot_state_trans e s (Some?.v osst')

(*
 * a consistent log that uses/references slots in a correct way:
 *  (a) Add associates a slot with a key
 *  (b) a slot is evicted if it is currently associated with a key
 *  (c) a slot is referenced in get/put and add/evict (as an ancestor) only if it is currently associated with a keys
 *  (d) An add is over a currently free slot
 *  (e) the definition uses an initial slot -> state mapping; we do not start with a mapping where all slots are free since
 *      we want to start verifier thread 0 with Root in slot 0
 *)
let consistent_log #vcfg (init_map: slot_state_map vcfg) (l:logS vcfg) =
  forall (s:slot_id vcfg). {:pattern slot_state_trans_closure s l (init_map s)}  slot_state_trans_closure s l (init_map s) <> None

(* a consistent log maps an initial slot_state_map to another slot_state_map *)
let to_slot_state_map #vcfg (init_map: slot_state_map vcfg) (l:logS vcfg{consistent_log init_map l}): slot_state_map _ =
  fun s -> Some?.v (slot_state_trans_closure s l (init_map s))

(* prefix of a consistent log is consistent *)
val lemma_consistent_log_prefix_consistent (#vcfg:_) (init_map: slot_state_map vcfg) (l:logS vcfg) (i:nat{i <= length l}):
  Lemma (requires (consistent_log init_map l))
        (ensures (consistent_log init_map (prefix l i)))

(* consistent logs can be mapped to spec-level log by replacing all slot references to the assoc'ed keys *)
val to_logk (#vcfg:_) (init_map: slot_state_map vcfg) (l:logS vcfg{consistent_log init_map l}): logK

val lemma_to_logk_length (#vcfg:_) (init_map: slot_state_map vcfg) (l:logS vcfg{consistent_log init_map l}):
  Lemma (ensures (length (to_logk init_map l) = length l))
        [SMTPat (to_logk init_map l)]

val lemma_all_entries_valid (#vcfg:_) (init_map: slot_state_map vcfg) (l:logS vcfg{consistent_log init_map l}) (i:seq_index l):
  Lemma (ensures (let l' = prefix l i in
                  lemma_consistent_log_prefix_consistent init_map l i;
                  let ssm' = to_slot_state_map init_map l' in
                  valid_logS_entry ssm' (index l i)))

val lemma_to_logk_index (#vcfg:_) (init_map: slot_state_map vcfg) (l:logS _{consistent_log init_map l}) (i:seq_index l):
  Lemma (ensures (let lk = to_logk init_map l in
                  let l' = prefix l i in
                  lemma_consistent_log_prefix_consistent init_map l i;
                  let ssm' = to_slot_state_map init_map l' in
                  lemma_all_entries_valid init_map l i;
                  index lk i = to_logK_entry ssm' (index l i)))
