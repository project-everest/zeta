module Zeta.High.Verifier

open Zeta.App
open Zeta.Time
open Zeta.Thread
open Zeta.Key
open Zeta.GenKey
open Zeta.Record
open Zeta.HashFunction

(* for records in the store, how were they added? *)
type add_method =
  | MAdd: add_method       (* AddM *)
  | BAdd: add_method         (* AddB *)

let compatible #aprm (k:base_key) (r:record aprm)
  = let kr,_ = r in
    to_base_key kr = k

(* verifier store entry indexed by a key k *)
type vstore_entry (aprm: app_params) (k:base_key) = {
  r:  r:record aprm {compatible k r};
  am: add_method;
}

(* verifier store is a subset of (k,v) records *)
(* we also track how the key was added merkle/blum *)
let store_t (aprm: app_params) = (k:base_key) -> option (vstore_entry aprm k)

(* does the store contain a key *)
let store_contains (#aprm: app_params) (st:store_t aprm) (k:base_key)
  = Some? (st k)

(* lookup the value of a key in the store *)
let stored_value (#aprm: app_params) (st:store_t aprm) (k:base_key {store_contains st k})
  = let _, v = (Some?.v (st k)).r in
    v

(* add method of a key in the store *)
let add_method_of (#aprm: app_params) (st:store_t aprm) (k:base_key {store_contains st k})
  = (Some?.v (st k)).am

(* update the store *)
let update_store (#aprm: app_params)
                 (st:store_t aprm)
                 (k:base_key {store_contains st k})
                 (r:record aprm {compatible k r}):
  Tot (st':store_t aprm {store_contains st' k /\ stored_value st' k = (value_of r)})
  = let am = add_method_of st k in
    fun k' -> if k' = k then Some ( { r; am } ) else st k'

(* add a new record to the store *)
let add_to_store (#aprm: app_params)
                 (st:store_t aprm)
                 (r: record aprm)
                 (am:add_method):
  (st':store_t aprm {let k,v = r in
                     let k = to_base_key k in
                     store_contains st' k /\ stored_value st' k = v})
  = let k,_ = r in
    let k = to_base_key k in
    fun k' -> if k' = k then Some ({ r; am }) else st k'

(* evict a key from a store *)
let evict_from_store (#aprm: app_params)
                     (st:store_t aprm)
                     (k:base_key {store_contains st k}) =
  fun k' -> if k' = k then None else st k'

(* per-thread state of the high-level verifier *)
noeq type vtls_t (app: app_params) = {
  (* is the verifier valid *)
  valid: bool;

  (* thread id *)
  tid: thread_id;

  (* clock *)
  clock: timestamp;

  (* verifier store *)
  st: store_t app;
}

let fail (#aprm: app_params) (vtls: vtls_t aprm)
  = { valid = false; tid = vtls.tid; clock = vtls.clock; st = vtls.st }

(* update the store of a specified verifier thread *)
let update_thread_store
  (#aprm: app_params)
  (vtls:vtls_t aprm {vtls.valid})
  (st:store_t aprm)
  = { valid = vtls.valid; tid = vtls.tid; clock = vtls.clock; st = st  }

let update_thread_clock
  (#aprm: app_params)
  (vtls:vtls_t aprm {vtls.valid})
  (clock: timestamp)
  = { valid = vtls.valid; tid = vtls.tid; clock ; st = vtls.st  }

let addm (#aprm: app_params)
         (r:record aprm)
         (k: base_key)
         (k': base_key)
         (vs: vtls_t aprm {vs.valid}): vtls_t aprm
  = let st = vs.st in
    let open Zeta.BinTree in
    let open Zeta.Merkle in
    (* the key of the record should be compatible with the "slot" k *)
    if not (compatible k r) then fail vs
    (* check k is a proper desc of k' *)
    else if not (is_proper_desc k k') then fail vs
    (* check store contains k' *)
    else if not (store_contains st k') then fail vs
    (* check store does not contain k *)
    else if store_contains st k then fail vs
    else
      let v = value_of r in
      let v' = to_merkle_value (stored_value st k') in
      let d = desc_dir k k' in
      let dh' = desc_hash v' d in
      let h = hashfn v in
      match dh' with
      | Empty ->
        if is_init_record r
        then
          let v' = update_value v' d k h false in
          let st = update_store st k' (IntK k', IntV v') in
          let st = add_to_store st r MAdd in
          update_thread_store vs st
        else
          fail vs
      | Desc k2 h2 b2 ->
        if k2 = k
        then
          if h2 = h && b2 = false then
            update_thread_store vs (add_to_store st r MAdd)
          else fail vs
        else if not (is_init_record r) then fail vs
        else if not (is_proper_desc k2 k) then fail vs
        else
          let d2 = desc_dir k2 k in
          let mv = to_merkle_value v in
          let mv = update_value mv d2 k2 h2 b2 in
          let v' = update_value v' d k h false in
          let st = update_store st k' (IntK k', IntV  v') in
          let st = add_to_store st (IntK k, (IntV mv)) MAdd in
          update_thread_store vs st

(* key k is in store and was added using Merkle *)
let is_instore_madd (#aprm: app_params) (st: store_t aprm) (k: base_key)
  = store_contains st k &&
    add_method_of st k = MAdd

let has_instore_merkle_desc
  (#aprm: app_params)
  (st: store_t aprm)
  (k: base_key {store_contains st k})
  = let open Zeta.Key in
    if is_leaf_key k then false
    else
      let v = to_merkle_value (stored_value st k) in
      let open Zeta.Merkle in
      let open Zeta.BinTree in
      let ld = desc_hash v Left in
      let rd = desc_hash v Right in
      Desc? ld && is_instore_madd st (Desc?.k ld) ||
      Desc? rd && is_instore_madd st (Desc?.k rd)

let evictm (#aprm: app_params)
           (k:base_key)
           (k':base_key)
           (vs: vtls_t aprm  {vs.valid}): vtls_t aprm
  = let st = vs.st in
    let open Zeta.BinTree in
    (* check store contains k and k' *)
    if not (store_contains st k && store_contains st k') then fail vs
    else if not (is_proper_desc k k') then fail vs
    else if has_instore_merkle_desc st k then fail vs
    else
      let v' = to_merkle_value (stored_value st k') in
      let v = stored_value st k in
      let d = desc_dir k k' in
      let open Zeta.Merkle in
      let dh' = desc_hash v' d in
      let h = hashfn v in
      match dh' with
      | Empty -> fail vs
      | Desc k2 h2 b2 -> if k2 = k then
                           let v' = update_value v' d k h false in
                           let st = evict_from_store (update_store st k' (IntK k', IntV v')) k in
                           update_thread_store vs st
                        else fail vs

let addb (#aprm: app_params)
         (r:record aprm)
         (k: base_key)
         (t:timestamp)
         (j:thread_id)
         (vs:vtls_t aprm {vs.valid}): vtls_t aprm
  = let st = vs.st in
    let open Zeta.BinTree in
    (* the key of the record r has to be k or its hash has to be k (for app records) *)
    if not (compatible k r) then fail vs
    (* never add Root *)
    else if k = Root then fail vs
    (* check store does not contain k *)
    else if store_contains st k then fail vs
    else
      (* updated clock max of current, 1 + t *)
      let clk = max vs.clock (next t) in
      (* update verifier state with new clock *)
      let vs = update_thread_clock vs clk in
      (* add record to store *)
      let st = add_to_store st r BAdd in
      update_thread_store vs st

let evictb_aux (#aprm: app_params)
               (k:base_key)
               (t:timestamp)
               (eam:add_method)
               (vs:vtls_t aprm {vs.valid}): vtls_t aprm
  = let st = vs.st in
    let open Zeta.BinTree in
    if k = Root then fail vs
    else if not (ts_lt vs.clock t) then fail vs
    else if not (store_contains st k) then fail vs
    else if add_method_of st k <> eam then fail vs
    else if has_instore_merkle_desc st k then fail vs
    else
      let vs = update_thread_clock vs t in
      let st = evict_from_store st k in
      update_thread_store vs st

let evictb (#aprm: app_params)
           (k:base_key)
           (t:timestamp)
           (vs:vtls_t aprm {vs.valid}): vtls_t aprm
  = evictb_aux k t BAdd vs

let evictbm (#aprm: app_params)
            (k:base_key)
            (k':base_key)
            (t:timestamp)
            (vs:vtls_t  aprm {vs.valid}): vtls_t aprm
  = let st = vs.st in
    let open Zeta.BinTree in
    if not (store_contains st k') then fail vs
    else if not (is_proper_desc k k') then fail vs
    else if not (store_contains st k) then fail vs
    else if add_method_of st k <> MAdd then fail vs
    else if has_instore_merkle_desc st k then fail vs
    else
      let v' = to_merkle_value (stored_value st k') in
      let d = desc_dir k k' in
      let open Zeta.Merkle in
      let dh' = desc_hash v' d in
      match dh' with
      | Empty ->
        fail vs
      | Desc k2 h2 b2 ->
        if k2 = k && b2 = false then
          let v' = update_value v' d k h2 true in
          let st = update_store st k' (IntK k', IntV v') in
          evictb_aux k t MAdd (update_thread_store vs st)
        else fail vs

let next_epoch (#aprm: app_params) (vs: vtls_t aprm{vs.valid})
  = let e = vs.clock.e + 1 in
    let clock = { e; c = 0 } in
    update_thread_clock vs clock

let verify_epoch (#aprm: app_params) (vs: vtls_t aprm{vs.valid})
  = vs
