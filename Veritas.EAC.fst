module Veritas.EAC

open FStar.Seq
open Veritas.Hash
open Veritas.Interleave
open Veritas.Key
open Veritas.MultiSetHash
open Veritas.Record
open Veritas.SeqAux
open Veritas.SeqMachine
open Veritas.State
open Veritas.StateSeqMachine
open Veritas.Verifier

//Allow the solver to unroll recursive functions at most once (fuel)
//Allow the solver to invert inductive definitions at most once (ifuel)
#push-options "--max_fuel 1 --max_ifuel 1 --initial_fuel 1 --initial_ifuel 1"

let is_evict (e: vlog_entry) = 
  match e with
  | EvictM _ _ -> true
  | EvictB _ _ -> true
  | EvictBM _ _ _ -> true
  | _ -> false

type evict_vlog_entry = e:vlog_entry {is_evict e}
type nevict_vlog_entry = e:vlog_entry {not (is_evict e)}

type vlog_entry_ext =
  | NEvict: e:nevict_vlog_entry -> vlog_entry_ext
  | Evict: e:evict_vlog_entry -> v:value -> vlog_entry_ext

type vlog_ext = seq (vlog_entry_ext)

type eac_state = 
  | EACFail: eac_state  
  | EACInit: eac_state
  | EACInCache: m:add_method -> v:value -> eac_state
  | EACEvicted: m:add_method -> v:value -> eac_state

let eac_add (e: vlog_entry_ext) (s: eac_state) : eac_state = 
  match s with
  | EACFail -> EACFail
  | EACInit -> (
    match e with 
    | NEvict (AddM (k,v) _) -> if v = init_value k then EACInCache MAdd v
                               else EACFail
    | _ -> EACFail
    )
  
  | EACInCache m v -> (
    match e with 
    | NEvict (Get _ v') -> if (DVal v') = v then s
                           else EACFail
    | NEvict (Put _ v') -> EACInCache m (DVal v')                   
    | Evict (EvictM _ _) v' -> if DVal? v && v' <> v then EACFail
                               else EACEvicted MAdd v
    | Evict (EvictBM _ _ _) v' -> if DVal? v && v' <> v || m <> MAdd then EACFail
                                  else EACEvicted BAdd v
    | Evict (EvictB _ _) v' ->  if DVal? v && v' <> v || m <> BAdd then EACFail
                                else EACEvicted BAdd v
    | _ -> EACFail
    )
  
  | EACEvicted m v -> (
    match e with
    | NEvict (AddM (_,v') _) -> if v' = v && m = MAdd then EACInCache MAdd v
                                else EACFail
    | NEvict (AddB (_,v') _ _) -> if v' = v && m = BAdd then EACInCache BAdd v
                                else EACFail
    | _ -> EACFail
  )

let eac_smk = SeqMachine EACInit EACFail eac_add

let to_vlog_entry (ee:vlog_entry_ext) = 
  match ee with
  | Evict e _ -> e
  | NEvict e -> e

let vlog_entry_key (e: vlog_entry_ext) = 
  match (to_vlog_entry e) with
  | Get k _ -> k
  | Put k _ -> k
  | AddM (k,_) _ -> k
  | EvictM k _ -> k
  | AddB (k,_) _ _ -> k
  | EvictB k _ -> k
  | EvictBM k _ _ -> k

let eac_sm = PSM eac_smk vlog_entry_key

(* evict add consistency *)
let eac (l:vlog_ext) = valid_all eac_sm l

(* refinement of evict add consistent logs *)
type eac_log = l:vlog_ext{eac l}

(* the state operations of a vlog *)
let is_state_op (e: vlog_entry) = 
  match e with
  | Get k v -> true
  | Put k v -> true 
  | _ -> false

(* map vlog entry to state op *)
let to_state_op (e:vlog_entry {is_state_op e}) = 
  match e with
  | Get k v -> Veritas.State.Get k v
  | Put k v -> Veritas.State.Put k v

(* filter out the state ops of vlog *)
let to_state_op_vlog (l: vlog) = 
  map to_state_op (filter_refine is_state_op l)

(* valid eac states *)
let valid_eac_state (st:eac_state) = not (EACFail? st)

(* value of a valid state *)
let value_of (st:eac_state {valid_eac_state st}) =
  match st with
  | EACInit -> DVal Null
  | EACInCache _ v -> v
  | EACEvicted _ v -> v

let to_vlog (l:vlog_ext) = 
  map to_vlog_entry l

let rec lemma_comm (le:vlog_ext) (k:data_key):
  Lemma (to_state_op_vlog (to_vlog (partn eac_sm k le)) = 
         partn ssm k (to_state_op_vlog (to_vlog le))) = 
  let lek = partn eac_sm k le in
  let lk = to_vlog lek in
  let lks = to_state_op_vlog lk in
  let l = to_vlog le in
  let ls = to_state_op_vlog l in
  let lsk = partn ssm k ls in
  admit()

  
let lemma_eac_k_implies_ssm_k_valid (le:eac_log) (k:data_key):
  Lemma (valid ssm_k (to_state_op_vlog (to_vlog (partn eac_sm k le)))) = 
  let lek = partn eac_sm k le in
  let lk = to_vlog lek in
  let lks = to_state_op_vlog lk in
  if valid ssm_k lks then ()
  else (
    let i = max_valid_prefix ssm_k lks in  
    let op = index lks i in
    let ssti = seq_machine_run ssm_k (prefix lks (i + 1)) in
    assert(ssti = StateFail);
    
    let ssti' = seq_machine_run ssm_k (prefix lks i) in
    if i = 0 then (
      lemma_reduce_singleton StateInit apply_state_op (prefix lks (i + 1));
      assert(StateFail = apply_state_op op StateInit);
      assert(Veritas.State.Get? op && Veritas.State.Get?.v op <> Null);
      admit()
    )
    else admit()
  )

(* evict add consistency implies rw-consistency *)
let lemma_eac_implies_rw_consistent (le:eac_log):
  Lemma (rw_consistent (to_state_op_vlog (to_vlog le))) = 
  let l = to_vlog le in
  let s = to_state_op_vlog l in
  let rwc = valid_all_comp ssm s in
  lemma_state_sm_equiv_rw_consistent s;
  if rwc then () // nothing to prove if rw_consistent
  else (
    (* invalidating key *)
    let k: data_key = invalidating_key ssm s in
    lemma_eac_k_implies_ssm_k_valid le k;    
    lemma_comm le k
  )
