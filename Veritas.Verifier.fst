module Veritas.Verifier

open FStar.Seq
open Veritas.Key
open Veritas.Record
open Veritas.SeqAux
open Veritas.MultiSetHash

(*
 * The verifier consumes a log that consists of memory operations and
 * additional "proof" objects and returns success of failure; we prove
 * that if the verifier returns success, then the underlying memory
 * operations are read-write consistent
 *)

(* Each entry of the verifier log *)
type vlog_entry =
  | Get: k:data_key -> v:data_value -> vlog_entry
  | Put: k:data_key -> v:data_value -> vlog_entry
  | AddM: r:record -> k':merkle_key -> vlog_entry
  | EvictM: k:key -> k':merkle_key -> vlog_entry 
  | AddB: r:record -> t:timestamp -> vlog_entry 
  | EvictB: k:key -> t:timestamp -> vlog_entry
  | EvictBM: k:key -> k':merkle_key -> vlog_entry

(* verifier log entry (global)  *)
type vlog_entry_g = 
  | Log: tid:nat -> e:vlog_entry -> vlog_entry_g

(* verifier log *)
type vlog = seq vlog_entry_g

(* index in the verifier log *)
type vl_index (l:vlog) = seq_index l

(* for records in the store, how were they added? *)
type add_method = 
  | Merkle: add_method       (* AddM *)
  | Blum: add_method         (* AddB *)

(* verifier store entry *)
type vstore_entry (k:key) = 
  | VStore: v:value_type_of k -> am: add_method -> vstore_entry k

(* verifier store is a subset of (k,v) records *)
(* we also track how the key was added merkle/blum *)
type vstore = (k:key) -> option (vstore_entry k)

(* does the store contain address a *)
let store_contains (st:vstore) (k:key) = Some? (st k)

(* lookup the value of a key in the store *)
let stored_value (st:vstore) (k:key{store_contains st k}):
  (value_type_of k) = 
  VStore?.v (Some?.v (st k))

(* add method of a key in the store *)
let add_method_of (st:vstore) (k:key{store_contains st k}): add_method = 
    VStore?.am (Some?.v (st k))

(* update the store *)
let update_store (st:vstore) 
                 (k:key{store_contains st k})
                 (v:value_type_of k):
  Tot (st':vstore {store_contains st' k /\ stored_value st' k = v}) = 
  let am = add_method_of st k in                      
  fun k' -> if k' = k then Some (VStore v am) else st k'

(* add a new record to the store *)
let add_to_store (st:vstore)
                 (k:key{not (store_contains st k)})
                 (v:value_type_of k)
                 (am:add_method): 
  (st':vstore{store_contains st' k /\ stored_value st' k = v}) =
  fun k' -> if k' = k then Some (VStore v am) else st k'

(* evict a key from a store *)
let evict_from_store (st:vstore)
                     (k:key{store_contains st k}) = 
  fun k' -> if k' = k then None else st k'

(* verifier thread local state  *)
noeq type vtls = 
  | TLS: st:vstore -> clk:timestamp -> lk:key -> vtls

(* per-epoch hash value *)
type epoch_hash = nat -> ms_hash_value

(* verifier global state *)
noeq type vgs = 
  | GS: hadd: epoch_hash -> 
        hevict: epoch_hash ->
        ne:nat -> vgs

(* verifier state aggregated across all verifier threads *)
noeq type vstate (p:nat) = 
  | Failed: vstate p
  | Valid: tlss:seq vtls{length tlss = p} ->
           gs:vgs ->
           vstate p

let thread_store (#p:nat) (i:nat{i < p}) (vs:vstate p{Valid? vs}): vstore = 
  let tlss = Valid?.tlss vs in
  let tls = index tlss i in
  TLS?.st tls  

(* verifier read operation; return false on verification failure *)
let vget (#p:nat) (i:nat{i < p}) 
         (k:data_key) (v:data_value) (vs: vstate p{Valid? vs}): vstate p =
  let st = thread_store i vs in
  
  (* check store contains addr *)
  if not (store_contains st k) then Failed
  
  (* check stored payload is v *)
  else if stored_value st k <> Data v then Failed 
  
  else vs

(*
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

let verifier_evictm (s: vstore)
                    (a:merkle_addr)
                    (a':merkle_addr): option vstore = 
  (* check store contains a and a' *)
  if not (store_contains s a && store_contains s a') then None
  else if is_merkle_root a then None
  else if not (is_proper_desc a a') then None
  else (
    lemma_proper_desc_depth_monotonic a a';
    assert(not (is_merkle_leaf a'));

    let v' = stored_payload s a' in
    let v = stored_payload s a in
    let d = desc_dir a a' in
    
    lemma_proper_desc_depth_monotonic a a';
    assert(not (is_merkle_leaf a'));
    
    let dh' = desc_hash_dir d v' in
    let h = hashfn v in

    match dh' with
    | Empty -> None
    | Desc a2 h2 b2 -> if a2 = a then 
                         let v'_upd = update_desc_hash v' d a h in
                         Some (store_evict (store_update s a' v'_upd) a)                       
                       else None    
  )

let verifier_addb (#p:nat) 
                  (i:nat {i < p}) 
                  (vs: vstate p{Valid? vs})
                  (a:merkle_addr)
                  (v:merkle_payload_of_addr a)
                  (t:timestamp): (vstate p) = 
  let tss = Valid?.tss vs in
  (* thread state *)
  let ts = index tss i in
  (* global state *)
  let gs = Valid?.gs vs in
  (* epoch of timestamp of last evict *)
  let e = MkTimestamp?.e t in
  (* next verify epoch of verifier *)
  let ne = VerifierGlobal?.ne gs in

  (* check that epoch e is at least ne *)
  if e < ne then Failed

  (* check that epoch e is at most 1 larger than ne *)
  else if e + 1 > ne then Failed 

  else (
    let epidx = e % 2 in
    admit()
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
  | EvictM a a' -> let optStore = verifier_evictm store a a' in
                   (
                     match optStore with
                     | None -> Failed
                     | Some store' -> thread_update_store tid vs store'
                   )
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
*)
