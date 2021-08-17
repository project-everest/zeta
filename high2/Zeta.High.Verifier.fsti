module Zeta.High.Verifier

open Zeta.App
open Zeta.Time
open Zeta.Thread
open Zeta.Key
open Zeta.Record

(* union of internal (merkle) keys and app keys *)
type key (app: app_params) =
  | IntKey: k:merkle_key -> key app
  | AppKey: k: app_key app.adm -> key app

(* the record type once we fix a key *)
let record_t #aprm (k: key aprm)
  = match k with
    | IntKey k -> r: record aprm { Int? r /\ (let Int (mk, _) = r in mk = k) }
    | AppKey k -> r: record aprm { App? r /\ (let App (ak, _) = r in ak = k) }

(* for records in the store, how were they added? *)
type add_method =
  | MAdd: add_method       (* AddM *)
  | BAdd: add_method         (* AddB *)

(* verifier store entry *)
type vstore_entry (#aprm: app_params) (k:key aprm) =
  | VStore: r:record_t k -> am: add_method -> vstore_entry k

(* verifier store is a subset of (k,v) records *)
(* we also track how the key was added merkle/blum *)
let vstore (aprm: app_params) = (k:key aprm) -> option (vstore_entry k)

(* per-thread state of the high-level verifier *)
noeq type vtls (app: app_params) = {
  (* is the verifier valid *)
  valid: bool;

  (* thread id *)
  tid: thread_id;

  (* clock *)
  clock: timestamp;

  (* verifier store *)
  st: vstore app;
}
