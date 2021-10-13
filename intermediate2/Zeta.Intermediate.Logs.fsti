module Zeta.Intermediate.Logs

open FStar.Seq
open Zeta.SeqAux
open Zeta.Key
open Zeta.App
open Zeta.GenKey
open Zeta.Intermediate.VerifierConfig
open Zeta.Intermediate.SlotKeyRel
open Zeta.Intermediate.Verifier

module GV = Zeta.GenericVerifier
module HV = Zeta.High.Verifier


(* Definitions of different styles of verifier logs.
   - logK : contains only key references (defined in Veritas.Verifier)
   - logS: contains slot references
   - logL: contains slot references & low-level data structures (TODO) *)


let logK_entry = HV.vlog_entry

let logS vcfg = seq (logS_entry vcfg)

let logK vcfg = seq (logK_entry vcfg.app)

(* all slots in a seq associated with a key *)
let all_slots_assoc (#vcfg:_) (ssm: slot_state_map vcfg) (ss: seq (slot_id vcfg))
  = forall i. (is_assoc ssm (index ss i))

val all_slots_assoc_comp (#vcfg:_) (ssm: slot_state_map vcfg) (ss: seq (slot_id vcfg))
  : b:bool{b <==> all_slots_assoc ssm ss}

(*
 * Given a slot -> key mapping, we define a boolean whether a log entry is valid.
 * This definition checks if the slots are used correctly:
 * (a) We add to a slot only if it is free
 * (b) We evict from a slot only if it is associated with a key
 * (c) We reference a slot in Get/Put and as an ancestor in Add/Evict only if it is associated with a key
 *)
let valid_logS_entry #vcfg (ssm: slot_state_map vcfg) (e: logS_entry vcfg): bool =
  let open Zeta.GenericVerifier in
  match e with
  | AddM r s s' ->
    is_free ssm s && is_assoc ssm s'
  | AddB r s  _ _ ->
    is_free ssm s
  | EvictM s s' ->
    is_assoc ssm s && is_assoc ssm s'
  | EvictB s _ ->
    is_assoc ssm s
  | EvictBM s s' _ ->
    is_assoc ssm s && is_assoc ssm s'
  | RunApp _ _ ss ->
    all_slots_assoc_comp ssm ss
  | VerifyEpoch
  | NextEpoch -> true

let to_key (#vcfg:_) (ssm: slot_state_map vcfg) (ss: seq (slot_id vcfg) {all_slots_assoc ssm ss}) (i: seq_index ss)
  : base_key
  = let s = index ss i in
    assert(is_assoc ssm s);
    assoc_key ssm s

let to_key_seq (#vcfg:_) (ssm: slot_state_map vcfg) (ss: seq (slot_id vcfg){all_slots_assoc ssm ss})
  : seq base_key
  = init (length ss) (to_key ssm ss)

let to_logk_entry #vcfg (ssm: slot_state_map vcfg) (e: logS_entry vcfg{valid_logS_entry ssm e})
  : logK_entry vcfg.app
  = let open Zeta.GenericVerifier in
    let vspec = HV.high_verifier_spec vcfg.app in
    match e with
    | AddM (gk,gv) s s' -> AddM (gk,gv) (to_base_key gk)  (assoc_key ssm s')
    | AddB (gk,gv) s t j -> AddB (gk,gv) (to_base_key gk) t j
    | EvictM s s' -> EvictM (assoc_key ssm s) (assoc_key ssm s')
    | EvictB s t -> EvictB (assoc_key ssm s) t
    | EvictBM s s' t -> EvictBM (assoc_key ssm s) (assoc_key ssm s') t
    | VerifyEpoch -> VerifyEpoch
    | NextEpoch -> NextEpoch
    | RunApp f p ss -> let ks: seq (vspec.slot_t) = to_key_seq ssm ss in
                       let f: appfn_id vspec.app = f in
                       RunApp f p ks

(*
 * define a state machine over slot_states; to allow for "failures" where the log
 * uses slot states in an inconsistent manner (e.g., evict a slot without adding to it)
 * we make the transition function return option slot_state, with None being failure.
 *)
let slot_state_trans #vcfg (e:logS_entry vcfg) (s:slot_id vcfg) (sst: slot_state): option slot_state =
  let open Zeta.GenericVerifier in
  match e with
  | AddM (gk,_) s1 s2 ->
    let k = to_base_key gk in
    if s = s1 then
      if Free? sst then Some (Assoc k)
      else None
    else if s = s2 then
      if Assoc? sst then Some sst
      else None
    else Some sst
  | AddB (gk,_) s1  _ _ ->
    let k = to_base_key gk in
    if s = s1 then
      if Free? sst then Some (Assoc k)
      else None
    else Some sst
  | EvictM s1 s2 ->
    if s = s1 then
      if Assoc? sst then Some Free
      else None
    else if s = s2 then
      if Assoc? sst then Some sst
      else None
    else Some sst
  | EvictB s1 _ ->
    if s = s1 then
      if Assoc? sst then Some Free
      else None
    else Some sst
  | EvictBM s1 s2 _ ->
    if s = s1 then
      if Assoc? sst then Some Free
      else None
    else if s = s2 then
      if Assoc? sst then Some sst
      else None
    else Some sst
  | RunApp _ _ _
  | NextEpoch
  | VerifyEpoch -> Some sst

let has_distinct_slots #vcfg (e: logS_entry vcfg): bool =
  let open Zeta.GenericVerifier in
  match e with
  | AddM _ s s' -> s <> s'
  | EvictM s s' -> s <> s'
  | EvictBM s s' _ -> s <> s'
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
  forall (s:slot_id vcfg). slot_state_trans_closure s l (init_map s) <> None

(* a consistent log maps an initial slot_state_map to another slot_state_map *)
let to_slot_state_map #vcfg
  (init_map: slot_state_map vcfg)
  (l:logS vcfg{consistent_log init_map l})
  : slot_state_map _
  = fun s -> Some?.v (slot_state_trans_closure s l (init_map s))

(* prefix of a consistent log is consistent *)
val lemma_consistent_log_prefix_consistent (#vcfg:_)
  (init_map: slot_state_map vcfg)
  (l:logS vcfg) (i:nat{i <= length l})
  : Lemma (requires (consistent_log init_map l))
        (ensures (consistent_log init_map (prefix l i)))

(* consistent logs can be mapped to spec-level log by replacing all slot references to the assoc'ed keys *)
val to_logk (#vcfg:_) (init_map: slot_state_map vcfg) (l:logS vcfg{consistent_log init_map l}): logK vcfg

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
                  index lk i = to_logk_entry ssm' (index l i)))
