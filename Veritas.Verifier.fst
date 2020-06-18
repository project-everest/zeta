module Veritas.Verifier

open FStar.Seq
open FStar.BitVector
open FStar.Classical
open Veritas.SeqAux
open Veritas.Memory
open Veritas.BinTree
open Veritas.BinTreePtr
open Veritas.MerkleAddr
open Veritas.Verifier.Defs

(*
 * The verifier consumes a log that consists of memory operations and
 * additional "proof" objects and returns success of failure; we prove
 * that if the verifier returns success, then the underlying memory
 * operations are read-write consistent
 *)

(* Each entry of the verifier log *)
type vlog_entry_thread =
  | MemoryOp: o:memory_op -> vlog_entry_thread
  | AddM: a:merkle_addr -> v:merkle_payload -> a':merkle_addr -> vlog_entry_thread
  | EvictM: a:merkle_addr -> a':merkle_addr -> vlog_entry_thread

(* verifier log entry *)
type vlog_entry = 
  | VLogEntry: tid:nat -> e:vlog_entry_thread -> vlog_entry

(* single verifier log *)
type vlog = seq vlog_entry

(* index in the verifier log *)
type vl_index (l:vlog) = seq_index l

(* verifier store is a subset of merkle_addr, merkle_payloads *)
type vstore = (a:merkle_addr) -> option (merkle_payload_of_addr a)

(* does the store contain address a *)
let store_contains (store:vstore) (a:merkle_addr) = Some? (store a)

(* lookup the payload of an address in store *)
let stored_payload (store:vstore) (a:merkle_addr{store_contains store a}):
  (merkle_payload_of_addr a) = 
  Some?.v (store a)

(* update the store *)
let store_update (store:vstore) 
                 (a:merkle_addr{store_contains store a})
                 (v:merkle_payload_of_addr a):
  Tot (store':vstore {store_contains store' a /\ 
                      stored_payload store' a = v}) = 
  fun a' -> if a' = a then Some v else store a'

(* per-thread verifier state *)
noeq type vthread_state = 
  | VerifierThread: store:vstore -> clk:timestamp -> lk:merkle_addr -> vthread_state

(* get the store of a thread *)
let thread_store (ts: vthread_state): vstore = VerifierThread?.store ts

(* update the store of a thread *)
let thread_store_update (ts: vthread_state)
                        (a:merkle_addr{store_contains (thread_store ts) a})
                        (v:merkle_payload_of_addr a): 
  Tot (ts': vthread_state{store_contains (thread_store ts') a /\
                          stored_payload (thread_store ts') a = v}) = 
  match ts with
  | VerifierThread store clk lk -> 
    VerifierThread (store_update store a v) clk lk

type vglobal_state = 
  | VerifierGlobal: hadd0:ms_hash_value ->
           hevict0:ms_hash_value ->
           hadd1:ms_hash_value ->
           hevict1:ms_hash_value ->
           ne:nat -> vglobal_state

(* verifier state aggregated across all verifier threads *)
noeq type vstate (p:nat) = 
  | Failed: vstate p
  | Valid: ts:seq vthread_state{length ts = p} ->  (* thread-specific state *)
           gs:vglobal_state ->                     (* global state *)
           vstate p

let verifier_read (#p:nat) (a:addr) (v:payload) 
                  (tid:nat {tid < p}) 
                  (vs: vstate p{Valid? vs}): vstate p = 
  (* thread state *)
  let ts = index (Valid?.ts vs) tid in
  (* thread store *)
  let store = VerifierThread?.store ts in
  (* merkle addr *)
  let ma = addr_to_merkle_leaf a in
  (* check store contains addr *)
  let optPayload = store ma in

  match optPayload with
  | None -> Failed
  | Some v' -> if v = MkLeaf?.value v' then vs 
               else Failed      

let verifier_write (#p:nat) (a:addr) (v:payload)
                   (tid:nat {tid < p}) 
                   (vs: vstate p{Valid? vs}): vstate p = 
  (* thread state *)
  let ts = index (Valid?.ts vs) tid in
  (* thread store *)
  let store = VerifierThread?.store ts in
  (* merkle addr *)
  let ma = addr_to_merkle_leaf a in
  (* check store contains addr *)
  let optPayload = store ma in

  match optPayload with
  | None -> Failed
  | Some _ -> admit() 

let verifier_step_thread (#p:nat) 
                         (e:vlog_entry_thread) 
                         (tid:nat {tid < p}) 
                         (vs:vstate p{Valid? vs}): vstate p = 
  // thread state                         
  let ts = index (Valid?.ts vs) tid in
  // global state
  let gs = Valid?.gs vs in
  // thread store
  let store = VerifierThread?.store ts in
  match e with
  | MemoryOp o -> 
    (
    match o with
    | Read a v -> verifier_read a v tid vs      
    | Write a v -> admit()
    )
  | AddM _ _ _ -> 
    admit()
  | EvictM _ _ ->
    admit()

let verifier_step (#p:nat) (e:vlog_entry) (vs:vstate p): vstate p = 
  match vs with
  | Failed -> Failed              // propagate failures
  | Valid ts gs -> 
    match e with
    VLogEntry tid e' ->
      if tid >= p then  Failed   // invalid thread id       
      else verifier_step_thread e' tid vs        

(* verify a log from a specified initial state *)
let rec verifier_aux (#p:nat) (l:vlog) (vs:vstate p): Tot (vstate p)
  (decreases (length l)) = 
  let n = length l in
  if n = 0 then vs
  else
    let l' = prefix l (n - 1) in
    let vs' = verifier_aux l' vs in
    let e' = index l (n - 1) in
    verifier_step e' vs'

(* initialize verifier state *)
let init_vstate (p:nat): vstate p = admit()

let verifier (p:nat) (l:vlog): Tot (vstate p) = 
  verifier_aux l (init_vstate p)
