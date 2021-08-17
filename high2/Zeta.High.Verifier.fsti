module Zeta.High.Verifier

open Zeta.App
open Zeta.Time
open Zeta.Thread
open Zeta.GenKey
open Zeta.Record
open Zeta.HashFunction

(* for records in the store, how were they added? *)
type add_method =
  | MAdd: add_method       (* AddM *)
  | BAdd: add_method         (* AddB *)

(* verifier store entry indexed by a key k *)
type vstore_entry (#aprm: app_params) (k:key aprm) = {
  r:  r:record aprm {let kc,_ = r in kc = k};
  am: add_method;
}

(* verifier store is a subset of (k,v) records *)
(* we also track how the key was added merkle/blum *)
let store_t (aprm: app_params) = (k:key aprm) -> option (vstore_entry k)

(* does the store contain a key *)
let store_contains (#aprm: app_params) (st:store_t aprm) (k:key aprm)
  = Some? (st k)

(* lookup the value of a key in the store *)
let stored_value (#aprm: app_params) (st:store_t aprm) (k:key aprm{store_contains st k})
  = let _, v = (Some?.v (st k)).r in
    v

(* add method of a key in the store *)
let add_method_of (#aprm: app_params) (st:store_t aprm) (k:key aprm{store_contains st k})
  = (Some?.v (st k)).am

(* update the store *)
let update_store (#aprm: app_params) (st:store_t aprm)
                 (k:key aprm{store_contains st k})
                 (v:value_t k):
  Tot (st':store_t aprm {store_contains st' k /\ stored_value st' k = v})
  = let am = add_method_of st k in
    let r = k, v in
    fun k' -> if k' = k then Some ( { r; am } ) else st k'

(* add a new record to the store *)
let add_to_store (#aprm: app_params)
                 (st:store_t aprm)
                 (k:key aprm)
                 (v:value_t k)
                 (am:add_method):
  (st':store_t aprm {store_contains st' k /\ stored_value st' k = v})
  = let r = k,v in
    fun k' -> if k' = k then Some ({ r; am }) else st k'

(* evict a key from a store *)
let evict_from_store (#aprm: app_params)
                     (st:store_t aprm)
                     (k:key aprm{store_contains st k}) =
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

val fail (#aprm: app_params) (vtls: vtls_t aprm): v:vtls_t aprm{v.valid = false}

let addm (#aprm: app_params)
         (r:record aprm)
         (k: key)
         (k':key)
         (vs: vtls_t {vs.valid}): vtls_t aprm
  = let st = vs.st in
    let (kc,v) = r in
    let open Zeta.GenKey in
    let open Zeta.Merkle in
    (* the key of the record should be identical to "slot" k *)
    if k <> kc then fail vs
    (* check k is a proper desc of k' *)
    else if not (is_proper_desc k k') then fail vs
    (* check store contains k' *)
    else if not (store_contains st k') then fail vs
    (* check store does not contain k *)
    else if store_contains st k then fail vs
    else
      let v' = to_merkle_value (stored_value st k') in
      let d = desc_dir k k' in
      let dh' = desc_hash v' d in
      let h = hashfn v in
      match dh' with
      | Empty -> if v = init_value k then
                 let v'_upd = update_merkle_value v' d k h false in
                 let st_upd = update_store st k' (MVal v'_upd) in
                 let st_upd2 = add_to_store st_upd k v MAdd in
                 update_thread_store vs st_upd2
               else Failed
    | Desc k2 h2 b2 -> if k2 = k then
                         if h2 = h && b2 = false then
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
