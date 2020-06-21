module Veritas.Verifier

open FStar.Seq
open Veritas.BinTree
open Veritas.Key
open Veritas.Hash
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
  | AddB: r:record -> t:timestamp -> j:nat -> vlog_entry
  | EvictB: k:key -> t:timestamp -> vlog_entry
  | EvictBM: k:key -> k':merkle_key -> t:timestamp -> vlog_entry
  | VerifyEpoch: vlog_entry

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

(* get the store of a specified verifier thread *)
let thread_store (#p:nat) (i:nat{i < p}) (vs:vstate p{Valid? vs}): vstore =
  let tlss = Valid?.tlss vs in
  let tls = index tlss i in
  TLS?.st tls

let thread_clock (#p:nat) (i:nat{i < p}) (vs:vstate p{Valid? vs}) = 
  let tlss = Valid?.tlss vs in
  let tls = index tlss i in
  TLS?.clk tls

(* update the store of a specified verifier thread *)
let update_thread_store (#p:nat)
                        (i:nat{i < p})
                        (vs:vstate p{Valid? vs})
                        (st:vstore)
                        : vstate p =
  let tlss = Valid?.tlss vs in
  let gs = Valid?.gs vs in
  let tls = index tlss i in
  match tls with
  | TLS _ clk lk -> let tls' = TLS st clk lk in
                    let tlss' = upd tlss i tls' in
                    Valid tlss' gs

let update_thread_clock (#p:nat) (i:nat{i < p})
                        (vs:vstate p{Valid? vs})
                        (clk:timestamp): vstate p = 
  let tlss = Valid?.tlss vs in
  let gs = Valid?.gs vs in
  let tls = index tlss i in
  match tls with
  | TLS st _ lk -> let tls' = TLS st clk lk in
                   let tlss' = upd tlss i tls' in
                   Valid tlss' gs

(* verifier read operation *)
let vget (#p:nat) (i:nat{i < p})
         (k:data_key) (v:data_value) (vs: vstate p{Valid? vs}): vstate p =
  let st = thread_store i vs in
  (* check store contains key *)
  if not (store_contains st k) then Failed
  (* check stored value is v *)
  else if to_data_value (stored_value st k) <> v then Failed
  (* all checks pass - simply return state unchanged *)
  else vs

let hadd (#p:nat) (e:nat) (vs:vstate p{Valid? vs}) = 
  let gs = Valid?.gs vs in
  let h = GS?.hadd gs in
  h e

let hevict (#p:nat) (e:nat) (vs:vstate p{Valid? vs}) = 
  let gs = Valid?.gs vs in
  let h = GS?.hevict gs in
  h e

let update_epoch_hash (eh: epoch_hash) (e:nat) (h:ms_hash_value) = 
  fun e' -> if e = e' then h else eh e'

let update_hadd (#p:nat) (e:nat) (h: ms_hash_value)  (vs:vstate p{Valid? vs}): vstate p = 
  match vs with
  | Valid tlss gs -> match gs with
                    | GS ha he ne -> let gs' = GS (update_epoch_hash ha e h) he ne in
                                     Valid tlss gs'

let update_hevict (#p:nat) (e:nat) (h:ms_hash_value) (vs:vstate p{Valid? vs}): vstate p = 
  match vs with
  | Valid tlss gs -> match gs with
                    | GS ha he ne -> let gs' = GS ha (update_epoch_hash he e h) ne in
                                     Valid tlss gs'

let update_ne (#p:nat) (ne:nat) (vs:vstate p{Valid? vs}): vstate p = 
  match vs with
  | Valid tlss gs -> match gs with
                    | GS ha he _ -> let gs' = GS ha he ne in
                                     Valid tlss gs'
  
(* verifier write operation *)
let vput (#p:nat) (i:nat{i < p})
         (k:data_key) (v:data_value) (vs: vstate p{Valid? vs}): vstate p =
  let st = thread_store i vs in
  (* check store contains key *)
  if not (store_contains st k) then Failed
  else update_thread_store i vs (update_store st k (DVal v))

(* update merkle value *)
let update_merkle_value (v:merkle_value)
                        (d:bin_tree_dir)
                        (k:key)
                        (h:hash_value)
                        (b:bool) =
  match v with
  | MkValue dhl dhr -> match d with
                      | Left -> MkValue (Desc k h b) dhr
                      | Right -> MkValue dhl (Desc k h b)

let vaddm (#p:nat) (i:nat{i < p})
          (r:record)
          (k':merkle_key)
          (vs: vstate p{Valid? vs}): vstate p =
  let st = thread_store i vs in
  let (k,v) = r in
  (* check k is a proper desc of k' *)
  if not (is_proper_desc k k') then Failed
  (* check store contains k' *)
  else if not (store_contains st k') then Failed
  (* check store does not contain k *)
  else if store_contains st k then Failed
  (* check that type of value is consistent with key *)
  else if not (is_value_of k v) then Failed
  else
    let v' = to_merkle_value (stored_value st k') in
    let d = desc_dir k k' in
    let dh' = desc_hash_dir v' d in
    let h = hashfn v in
    match dh' with
    | Empty -> if v = init_value k then
                 let v'_upd = update_merkle_value v' d k h false in
                 let st_upd = update_store st k' (MVal v'_upd) in
                 let st_upd2 = add_to_store st_upd k v Merkle in
                 update_thread_store i vs st_upd2
               else Failed
    | Desc k2 h2 b2 -> if k2 = k then
                         if h2 = h then
                           update_thread_store i vs (add_to_store st k v Merkle)
                         else Failed
                       else if v <> init_value k then Failed
                       else if not (is_proper_desc k2 k) then Failed
                       else
                         let d2 = desc_dir k2 k in
                         let mv = to_merkle_value v in
                         let mv_upd = update_merkle_value mv d2 k2 h2 b2 in
                         let v'_upd = update_merkle_value v' d k h false in
                         let st_upd = update_store st k'(MVal  v'_upd) in
                         let st_upd2 = add_to_store st_upd k (MVal mv_upd) Merkle in
                         update_thread_store i vs st_upd2

let vevictm (#p:nat) (i:nat{i < p})
            (k:key)
            (k':merkle_key)
            (vs: vstate p{Valid? vs}): vstate p = 
  let st = thread_store i vs in
  (* check store contains a and a' *)
  if not (store_contains st k && store_contains st k') then Failed
  else if not (is_proper_desc k k') then Failed
  else
    let v' = to_merkle_value (stored_value st k') in
    let v = stored_value st k in
    let d = desc_dir k k' in
    let dh' = desc_hash_dir v' d in
    let h = hashfn v in
    match dh' with
    | Empty -> Failed
    | Desc k2 h2 b2 -> if k2 = k then
                         let v'_upd = update_merkle_value v' d k h b2 in
                         let st_upd = evict_from_store (update_store st k' (MVal v'_upd)) k in
                         update_thread_store i vs st_upd
                       else Failed

let max (t1 t2: timestamp) = 
  if t1 `ts_lesser` t2 then t2 else t1

let vaddb (#p:nat) (i:nat{i < p})
          (r:record)
          (t:timestamp)
          (j:nat)
          (vs:vstate p{Valid? vs}): vstate p = 
  (* global state *)
  let gs = Valid?.gs vs in          
  (* epoch of timestamp of last evict *)
  let e = MkTimestamp?.e t in
  (* next verify epoch of verifier *)
  let ne = GS?.ne gs in
  let st = thread_store i vs in  
  let (k,v) = r in
  (* check value type consistent with key k *)
  if not (is_value_of k v) then Failed
  (* check that epoch e is at least ne *)
  else if e < ne then Failed
  (* check store does not contain k *)
  else if store_contains st k then Failed
  else 
    (* current h_add *)
    let h = hadd e vs in
    (* updated h_add *)
    let h_upd = ms_hashfn_upd (MHDom r t j) h in
    (* update verifier state *)
    let vs_upd = update_hadd e h_upd vs in
    (* current clock of thread i *)
    let clk = thread_clock i vs in
    (* updated clock *)
    let clk_upd = max clk t in
    (* update verifier state with new clock *)
    let vs_upd2 = update_thread_clock i vs_upd clk_upd in
    (* add record to store *)
    let st_upd = add_to_store st k v Blum in
    update_thread_store i vs_upd2 st_upd

let vevictb (#p:nat) (i:nat{i < p})
            (k:key) (t:timestamp)
            (vs:vstate p{Valid? vs}): vstate p = 
  let gs = Valid?.gs vs in
  let clk = thread_clock i vs in
  let e = MkTimestamp?.e t in
  let ne = GS?.ne gs in
  let st = thread_store i vs in
  if not (ts_lesser clk t) then Failed
  else if e < ne then Failed  
  else if not (store_contains st k) then Failed  
  else 
    (* current h_evict *)
    let h = hevict e vs in
    let v = stored_value st k in
    let h_upd = ms_hashfn_upd (MHDom (k,v) t i) h in
    let vs_upd = update_hevict e h_upd vs in
    let vs_upd2 = update_thread_clock i vs_upd t in    
    let st_upd = evict_from_store st k in
    update_thread_store i vs_upd2 st_upd

let vevictbm (#p:nat) (i:nat{i < p})
             (k:key) (k':merkle_key) (t:timestamp)
             (vs:vstate p{Valid? vs}): vstate p = 
  let st = thread_store i vs in
  if not (store_contains st k') then Failed 
  else if not (is_proper_desc k k') then Failed
  else
    let v' = to_merkle_value (stored_value st k') in
    let d = desc_dir k k' in
    let dh' = desc_hash_dir v' d in
    match dh' with
    | Empty -> Failed
    | Desc k2 h2 b2 -> if k2 = k && b2 = false then
                         let v'_upd = update_merkle_value v' d k h2 true in
                         let st_upd = update_store st k' (MVal v'_upd) in
                         vevictb i k t (update_thread_store i vs st_upd)
                       else Failed

let vverify_epoch (#p:nat) (vs:vstate p{Valid? vs}): vstate p = 
  let gs = Valid?.gs vs in
  let ne = GS?.ne gs in
  let ha = hadd ne vs in
  let he = hevict ne vs in
  if ha = he then
    update_ne (ne + 1) vs
  else Failed
 
let verifier_step_thread (#p:nat)
                         (e:vlog_entry)
                         (i:nat{i < p})
                         (vs:vstate p{Valid? vs}): vstate p =                           
  match e with
  | Get k v -> vget i k v vs
  | Put k v -> vput i k v vs
  | AddM r k'  -> vaddm i r k' vs
  | EvictM k k' -> vevictm i k k' vs
  | AddB r t j -> vaddb i r t j vs
  | EvictB k t -> vevictb i k t vs
  | EvictBM k k' t -> vevictbm i k k' t vs
  | VerifyEpoch -> vverify_epoch vs

let verifier_step (#p:nat) (e:vlog_entry_g) (vs:vstate p): vstate p =
  match vs with
  | Failed -> Failed              // propagate failures
  | Valid ts gs ->
    match e with
    | Log i e' ->
      if i >= p then  Failed   // invalid thread id
      else verifier_step_thread e' i vs

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

let init_epoch_hash = fun e -> empty_hash_value

let empty_store:vstore = fun (k:key) -> None

(* initialize verifier state *)
let init_vstate (p:nat{p > 0}): vstate p = 
  let gs = GS init_epoch_hash init_epoch_hash 0 in
  let tls = TLS empty_store (MkTimestamp 0 0) Root in  
  let tlss = create p tls in
  let vs:vstate p = Valid tlss gs in
  let st0 = thread_store 0 vs in
  let st0_upd = add_to_store st0 Root (init_value Root) Merkle in
  update_thread_store 0 vs st0_upd

let verifier (p:nat{p > 0}) (l:vlog): Tot (vstate p) =
  verifier_aux l (init_vstate p)

