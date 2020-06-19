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
  | AddB: a:merkle_addr -> v:merkle_payload -> t:timestamp -> vlog_entry_thread 
  | EvictB: a:merkle_addr -> t:timestamp -> vlog_entry_thread
  | EvictBM: a: merkle_addr -> a':merkle_addr -> t:timestamp -> vlog_entry_thread

(* verifier log entry *)
type vlog_entry = 
  | VLogEntry: tid:nat -> e:vlog_entry_thread -> vlog_entry

(* single verifier log *)
type vlog = seq vlog_entry

(* index in the verifier log *)
type vl_index (l:vlog) = seq_index l

(* for records in the store, how were they added? *)
type add_method = 
  | Merkle: add_method       (* AddM *)
  | Blum: add_method         (* AddB *)

(* information we keep for each addr in store *)
type vstore_payload (a:merkle_addr) = 
  | SP: v:merkle_payload_of_addr a -> add:add_method -> vstore_payload a

(* verifier store is a subset of merkle_addr, merkle_payloads *)
type vstore = (a:merkle_addr) -> option (vstore_payload a)

(* does the store contain address a *)
let store_contains (store:vstore) (a:merkle_addr) = Some? (store a)

(* lookup the payload of an address in store *)
let stored_payload (store:vstore) (a:merkle_addr{store_contains store a}):
  (merkle_payload_of_addr a) = 
  SP?.v (Some?.v (store a))

let stored_add_method (store:vstore) (a:merkle_addr{store_contains store a}): add_method = 
    SP?.add (Some?.v (store a))

(* update the store *)
let store_update (store:vstore) 
                 (a:merkle_addr{store_contains store a})
                 (v:merkle_payload_of_addr a):
  Tot (store':vstore {store_contains store' a /\ 
                      stored_payload store' a = v}) = 
  let am = stored_add_method store a in                      
  fun a' -> if a' = a then Some (SP v am) else store a'

(* add a new record to the store *)
let store_add (s:vstore)
              (a:merkle_addr{not(store_contains s a)})
              (v:merkle_payload_of_addr a)
              (am:add_method): (s':vstore{store_contains s' a}) =
  fun a' -> if a' = a then Some (SP v am) else s a'

(* per-thread verifier state *)
noeq type vthread_state = 
  | VerifierThread: store:vstore -> clk:timestamp -> lk:merkle_addr -> vthread_state

type vglobal_state = 
  | VerifierGlobal: hadd0:ms_hash_value ->
           hevict0:ms_hash_value ->
           hadd1:ms_hash_value ->
           hevict1:ms_hash_value ->
           ne:nat -> vglobal_state

(* verifier state aggregated across all verifier threads *)
noeq type vstate (p:nat) = 
  | Failed: vstate p
  | Valid: tss:seq vthread_state{length tss = p} ->  (* thread-specific state *)
           gs:vglobal_state ->                     (* global state *)
           vstate p

(* verifier read operation; return false on verification failure *)
let verifier_read (a:addr) (v:payload) 
                  (store: vstore): bool =
  (* merkle addr *)
  let ma = addr_to_merkle_leaf a in
  (* check store contains addr *)
  if not (store_contains store ma) then false
  (* check stored payload is v *)
  else stored_payload store ma = MkLeaf v

(* verification write operation: return updated store on success; Null on failure *)
let verifier_write (a:addr) (v:payload)
                   (store: vstore): option vstore = 
  (* merkle addr *)
  let ma = addr_to_merkle_leaf a in  
  (* check store contains addr *)
  if not (store_contains store ma) then None
  (* update the store *)
  else Some (store_update store ma (MkLeaf v))

let is_empty_or_null (a:merkle_addr) (v:merkle_payload_of_addr a): Tot bool =
  if is_merkle_leaf a then Null? (MkLeaf?.value v)
  else Empty? (MkInternal?.left v) &&
       Empty? (MkInternal?. right v)

let update_desc_hash (v:merkle_payload_internal)
                     (d:bin_tree_dir)
                     (a:merkle_addr)
                     (h:hash_value) =
  match v with
  | MkInternal dhl dhr -> match d with 
                         | Left -> MkInternal (Desc a h false) dhr
                         | Right -> MkInternal dhl (Desc a h false)

let verifier_addm (s: vstore) 
                  (a: merkle_addr)
                  (v: merkle_payload)
                  (a': merkle_addr): option vstore = 
  (* check a is a proper desc of a' *)                  
  if not (is_proper_desc a a') then None
  (* check store contains a' *)
  else if not (store_contains s a') then None
  (* check store does not contain a *)
  else if store_contains s a then None 
  (* Check the payload type corresponds to leaf/internal ness of address a *)
  else if not (is_payload_of_addr a v) then None
  
  else (
    let v' = stored_payload s a' in
    let d = desc_dir a a' in

    lemma_proper_desc_depth_monotonic a a';
    assert(not (is_merkle_leaf a'));
    
    let dh' = desc_hash_dir d v' in
    let h = hashfn v in

    match dh' with
    | Empty -> if (is_empty_or_null a v) then 
                 let v'_upd = update_desc_hash v' d a h in
                 let s_upd = store_update s a' v'_upd in
                 Some (store_add s_upd a v Merkle)
               else None
    | Desc a2 h2 b2 -> if a2 = a && h2 = h then Some (store_add s a v Merkle) 
                       else if not (is_empty_or_null a v) then None                        
                       else if not (is_proper_desc a2 a) then None
                       else (
                         lemma_proper_desc_depth_monotonic a2 a;
                         assert(not (is_merkle_leaf a));

                         let d2 = desc_dir a2 a in
                         let v_upd = update_desc_hash v d2 a2 h2 in
                         let v'_upd = update_desc_hash v' d a h in
                         let s_upd = store_update s a' v'_upd in
                         Some (store_add s_upd a v Merkle)
                       )
  )    
  

(* update the store of a specific thread *)
let thread_update_store (#p:nat) (tid:nat {tid < p}) 
                        (vs:vstate p{Valid? vs})
                        (store:vstore): vstate p = 
  let tss = Valid?.tss vs in
  let gs = Valid?.gs vs in
  let ts = index tss tid in
  match ts with
  | VerifierThread _ clk lk -> 
    let ts_upd = VerifierThread store clk lk in
    let tss_upd = upd tss tid ts_upd in
    Valid tss_upd gs

let verifier_step_thread (#p:nat) 
                         (e:vlog_entry_thread) 
                         (tid:nat {tid < p}) 
                         (vs:vstate p{Valid? vs}): vstate p = 
  let gs = Valid?.gs vs in
  let tss = Valid?.tss vs in
  let ts = index tss tid in
  let store = VerifierThread?.store ts in
  match e with
  | MemoryOp o -> 
    (
    match o with
    | Read a v -> if verifier_read a v store       
                  then vs
                  else Failed
    | Write a v -> let optStore = verifier_write a v store in
                   match optStore with
                   | None -> Failed
                   | Some store' -> thread_update_store tid vs store'    
    )
  | AddM a v a' -> let optStore = verifier_addm store a v a' in
                   (
                     match optStore with
                     | None -> Failed
                     | Some store' -> thread_update_store tid vs store'
                   )
  | EvictM _ _ ->
    admit()
  | _ -> admit()

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
