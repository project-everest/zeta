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

(* verifier log *)
type vlog = seq (vlog_entry)

(* index in the verifier log *)
type vl_index (l:vlog) = seq_index l

(* for records in the store, how were they added? *)
type add_method =
  | MAdd: add_method       (* AddM *)
  | BAdd: add_method         (* AddB *)

(* verifier store entry *)
type vstore_entry (k:key) =
  | VStore: v:value_type_of k -> am: add_method -> vstore_entry k

(* verifier store is a subset of (k,v) records *)
(* we also track how the key was added merkle/blum *)
type vstore = (k:key) -> option (vstore_entry k)

(* verifier thread local state  *)
noeq type vtls =
  | Failed
  | Valid: id:nat ->
           st:vstore -> 
           clk:timestamp -> 
           lk:key -> 
           hadd: ms_hash_value ->
           hevict: ms_hash_value ->
           vtls

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

let thread_id (vs:vtls {Valid? vs}): nat = 
  Valid?.id vs

(* get the store of a specified verifier thread *)
let thread_store (vs: vtls {Valid? vs}): vstore =
  Valid?.st vs

(* update the store of a specified verifier thread *)
let update_thread_store (vs:vtls {Valid? vs})
                        (st:vstore)
                        : vtls =
  match vs with
  | Valid id _ clk lk ha he -> Valid id st clk lk ha he

(* get the clock from verifier thread state *)
let thread_clock (vs:vtls {Valid? vs}) = 
  Valid?.clk vs

(* update the clock of the verifier *)
let update_thread_clock (vs:vtls {Valid? vs})
                        (clk:timestamp): vtls = 
  match vs with
  | Valid id st _ lk ha he -> Valid id st clk lk ha he

let thread_hadd (vs:vtls {Valid? vs}) = 
  Valid?.hadd vs

let thread_hevict (vs:vtls {Valid? vs}) = 
  Valid?.hevict vs

let update_thread_hadd (vs:vtls {Valid? vs}) (ha': ms_hash_value): vtls = 
  match vs with
  | Valid id st clk lk ha he -> Valid id st clk lk ha' he

let update_thread_hevict (vs:vtls {Valid? vs}) (he':ms_hash_value): vtls = 
  match vs with
  | Valid id st clk lk ha he -> Valid id st clk lk ha he'

(* verifier read operation *)
let vget (k:data_key) (v:data_value) (vs: vtls {Valid? vs}): vtls =
  let st = thread_store vs in
  (* check store contains key *)
  if not (store_contains st k) then Failed
  (* check stored value is v *)
  else if to_data_value (stored_value st k) <> v then Failed
  (* all checks pass - simply return state unchanged *)
  else vs
  
(* verifier write operation *)
let vput (k:data_key) (v:data_value) (vs: vtls {Valid? vs}): vtls =
  let st = thread_store vs in
  (* check store contains key *)
  if not (store_contains st k) then Failed
  else update_thread_store vs (update_store st k (DVal v))

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

let vaddm (r:record)
          (k':merkle_key)
          (vs: vtls {Valid? vs}): vtls =
  let st = thread_store vs in
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
                 let st_upd2 = add_to_store st_upd k v MAdd in
                 update_thread_store vs st_upd2
               else Failed
    | Desc k2 h2 b2 -> if k2 = k then
                         if h2 = h then
                           update_thread_store vs (add_to_store st k v MAdd)
                         else Failed
                       else if v <> init_value k then Failed
                       else if not (is_proper_desc k2 k) then Failed
                       else
                         let d2 = desc_dir k2 k in
                         let mv = to_merkle_value v in
                         let mv_upd = update_merkle_value mv d2 k2 h2 b2 in
                         let v'_upd = update_merkle_value v' d k h false in
                         let st_upd = update_store st k'(MVal  v'_upd) in
                         let st_upd2 = add_to_store st_upd k (MVal mv_upd) MAdd in
                         update_thread_store vs st_upd2

let vevictm (k:key)
            (k':merkle_key)
            (vs: vtls {Valid? vs}): vtls = 
  let st = thread_store vs in
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
                         update_thread_store vs st_upd
                       else Failed

let max (t1 t2: timestamp) = 
  if t1 `ts_lt` t2 then t2 else t1

let vaddb (r:record)
          (t:timestamp)
          (j:nat)
          (vs:vtls {Valid? vs}): vtls = 
  (* epoch of timestamp of last evict *)
  let e = MkTimestamp?.e t in
  let st = thread_store vs in  
  let (k,v) = r in
  (* check value type consistent with key k *)
  if not (is_value_of k v) then Failed
  (* check store does not contain k *)
  else if store_contains st k then Failed
  else 
    (* current h_add *)
    let h = thread_hadd vs in
    (* updated h_add *)
    let h_upd = ms_hashfn_upd (MHDom r t j) h in
    (* update verifier state *)
    let vs_upd = update_thread_hadd vs h_upd in
    (* current clock of thread i *)
    let clk = thread_clock vs in
    (* updated clock *)
    let clk_upd = max clk t in
    (* update verifier state with new clock *)
    let vs_upd2 = update_thread_clock vs_upd clk_upd in
    (* add record to store *)
    let st_upd = add_to_store st k v BAdd in
    update_thread_store vs_upd2 st_upd

let vevictb (k:key) (t:timestamp)
            (vs:vtls {Valid? vs}): vtls = 
  let clk = thread_clock vs in
  let e = MkTimestamp?.e t in
  let st = thread_store vs in
  if k = Root then Failed
  else if not (ts_lt clk t) then Failed
  else if not (store_contains st k) then Failed  
  else 
    (* current h_evict *)
    let h = thread_hevict vs in
    let v = stored_value st k in
    let h_upd = ms_hashfn_upd (MHDom (k,v) t (thread_id vs)) h in
    let vs_upd = update_thread_hevict vs h_upd in
    let vs_upd2 = update_thread_clock vs_upd t in    
    let st_upd = evict_from_store st k in
    update_thread_store vs_upd2 st_upd

let vevictbm (k:key) (k':merkle_key) (t:timestamp)
             (vs:vtls {Valid? vs}): vtls = 
  let st = thread_store vs in
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
                         vevictb k t (update_thread_store vs st_upd)
                       else Failed

(* thread-level verification step *)
let t_verify_step (vs:vtls)
                  (e:vlog_entry): vtls =                           
  match vs with
  | Failed -> Failed
  | _ ->
    match e with
    | Get k v -> vget k v vs
    | Put k v -> vput k v vs
    | AddM r k'  -> vaddm r k' vs
    | EvictM k k' -> vevictm k k' vs
    | AddB r t j -> vaddb r t j vs
    | EvictB k t -> vevictb k t vs
    | EvictBM k k' t -> vevictbm k k' t vs

(* verify a log from a specified initial state *)
let rec t_verify_aux (vs:vtls) (l:vlog): Tot vtls
  (decreases (length l)) =
  let n = length l in
  if n = 0 then vs
  else
    let l' = prefix l (n - 1) in
    let vs' = t_verify_aux vs l' in
    let e' = index l (n - 1) in
    t_verify_step vs' e'

let empty_store:vstore = fun (k:key) -> None

(* initialize verifier state *)
let init_thread_state (id:nat): vtls = 
  let vs = Valid id empty_store (MkTimestamp 0 0) Root empty_hash_value empty_hash_value in  
  if id = 0 then
    let st0 = thread_store vs in
    let st0_upd = add_to_store st0 Root (init_value Root) MAdd in
    update_thread_store vs st0_upd    
  else vs

let t_verify (id:nat) (l:vlog): vtls = 
  t_verify_aux (init_thread_state id) l 

(* TODO: move to a different location? *)
let vlog_entry_key (e:vlog_entry): key =
  match e with 
  | Get k _ -> k
  | Put k _ -> k
  | AddM (k,_) _ -> k
  | EvictM k _ -> k
  | AddB (k,_) _ _ -> k
  | EvictB k _ -> k
  | EvictBM k _ _ -> k

let is_evict (e: vlog_entry): bool =
  match e with
  | EvictM _ _ -> true
  | EvictB _ _ -> true
  | EvictBM _ _ _ -> true
  | _ -> false
  
let is_add (e:vlog_entry): bool = 
  match e with
  | AddM _ _ -> true
  | AddB _ _ _ -> true
  | _ -> false

let is_add_of_key (k: key) (e:vlog_entry): bool = 
  match e with
  | AddM (k,_) _ -> true
  | AddB (k,_) _ _ -> true
  | _ -> false 
