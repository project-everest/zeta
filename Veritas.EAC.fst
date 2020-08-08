module Veritas.EAC

open FStar.Seq
open Veritas.Hash
open Veritas.Interleave
open Veritas.Key
open Veritas.MultiSetHash
open Veritas.Record
open Veritas.SeqAux
open Veritas.State
open Veritas.Verifier

//Allow the solver to unroll recursive functions at most once (fuel)
//Allow the solver to invert inductive definitions at most once (ifuel)
#push-options "--max_fuel 1 --max_ifuel 1 --initial_fuel 1 --initial_ifuel 1"

type eac_state = 
  | EACFail: eac_state  
  | EACInit: eac_state
  | EACInCache: m:add_method -> k:key -> v:value -> eac_state
  | EACEvicted: m:add_method -> k:key -> v:value -> eac_state

let eac_add (e: vlog_entry) (s: eac_state) : eac_state = 
  match s with
  | EACFail -> EACFail
  | EACInit -> (
    match e with 
    | AddM (k,v) _ -> if v = init_value k then EACInCache MAdd k v
                      else EACFail
    | _ -> EACFail
  )
  
  | EACInCache m k v -> (
    match e with 
    | Get k' v' -> if k' = k && (DVal v') = v then s
                   else EACFail
    | Put k' v' -> if k' = k then EACInCache m k (DVal v')
                   else EACFail 
    | EvictM k' _ -> if k' = k then EACEvicted MAdd k v
                     else EACFail
    | EvictBM k' _ _ -> if k' = k && m = MAdd then EACEvicted BAdd k v
                        else EACFail
    | EvictB k' _ -> if k' = k && m = BAdd then EACEvicted BAdd k v
                     else EACFail
    | _ -> EACFail
  )
  
  | EACEvicted m k v -> (
    match e with
    | AddM (k',v') _ -> if k' = k && v' = v && m = MAdd then EACInCache MAdd k v
                        else EACFail
    | AddB (k',v') _ _ -> if k' = k && v' = v && m = BAdd then EACInCache BAdd k v
                          else EACFail
    | _ -> EACFail
  )
                                
let eac_verify (l: vlog) = reduce EACInit eac_add l

let eac_valid (l: vlog) = not (EACFail? (eac_verify l))

let vlog_entry_key (e: vlog_entry) = 
  match e with
  | Get k _ -> k
  | Put k _ -> k
  | AddM (k,_) _ -> k
  | EvictM k _ -> k
  | AddB (k,_) _ _ -> k
  | EvictB k _ -> k
  | EvictBM k _ _ -> k

let lemma_eac_fail_sticky ():
  Lemma (forall (e:vlog_entry). eac_add e EACFail = EACFail) = ()

let rec lemma_eac_valid_implies_prefix (l: vlog{eac_valid l}) (i: nat{i <= length l}):
  Lemma (requires True)
        (ensures (eac_valid (prefix l i)))
        (decreases (length l)) 
        [SMTPat (prefix l i)]
        = 
  let n = length l in
  if n = 0 then ()
  else if i = n then ()
  else 
    let l' = prefix l (n - 1) in
    if eac_valid l' then (
      lemma_eac_valid_implies_prefix l' i;
      ()
    )
    else (
      lemma_reduce_prefix EACInit eac_add l (n - 1);
      lemma_reduce_identity EACFail eac_add (suffix l 1)
    )

let invalid_or_attached_to (k: key) (s: eac_state) =
  match s with 
  | EACInit -> false
  | EACFail -> true
  | EACInCache _ k' _ -> k' = k
  | EACEvicted _ k' _ -> k' = k

let lemma_eac_invariant (k: key): 
  Lemma (forall s. forall e. invalid_or_attached_to k s ==> invalid_or_attached_to k (eac_add e s)) = ()

let lemma_eac_valid_implies_same_key (l: vlog) (i: seq_index l):
  Lemma (requires eac_valid l /\ length l > 0)
        (ensures (vlog_entry_key (index l i) = vlog_entry_key (index l 0)))
        (decreases (length l)) = 
  let e0 = index l 0 in
  let k = vlog_entry_key e0 in
  let li = prefix l (i + 1) in
  let s0 = eac_verify (prefix l 1) in
  lemma_eac_valid_implies_prefix l 1;
  lemma_reduce_singleton EACInit eac_add (prefix l 1);
  if i = 0 then ()
  else if i = 1 then (
    lemma_reduce_prefix EACInit eac_add li 1;
    lemma_reduce_singleton s0 eac_add (suffix li 1)
  )
  else ( 
    let li' = prefix l i in
    lemma_reduce_prefix EACInit eac_add li' 1;
    lemma_reduce_property_closure (invalid_or_attached_to k) s0 eac_add (suffix li' (i - 1));
    let si' = eac_verify li' in
    lemma_reduce_prefix EACInit eac_add li i;    
    lemma_reduce_singleton si' eac_add (suffix li 1)
  )

(* filter out entries of vlog affecting key k *)
let key_vlog (k: key) (l: vlog) = filter (fun e -> k = vlog_entry_key e) l

(* evict add consistency *)
let eac (l:vlog) = forall (k: key). ~(EACFail? (eac_verify (key_vlog k l)))

(* refinement of evict add consistent logs *)
type eac_log = l:vlog{eac l}

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

(* evict add consistency implies rw-consistency *)
let lemma_eac_implies_rw_consistent (l:eac_log):
  Lemma (rw_consistent (to_state_op_vlog l)) = admit()
