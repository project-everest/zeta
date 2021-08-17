module Zeta.Record

open FStar.BitVector
open Zeta.App
open Zeta.BinTree
open Zeta.Hash
open Zeta.Merkle
open Zeta.GenKey

type value (aprm: app_params) =
  | AppV: v: app_value_nullable aprm.adm -> value aprm
  | IntV: v: Merkle.value -> value aprm

let compatible #aprm (k: key aprm) (v: value aprm) =
  match k, v with
  | AppK _, AppV _ -> true
  | IntK _, IntV _ -> true
  | AppK _, IntV _ -> false
  | IntK _, AppV _ -> false

(* a record is a union of merkle (internal) record and app record *)
let record (aprm: app_params) =
  r:(key aprm & value aprm){ let k,v = r in compatible k v  }

let value_t (#aprm: app_params) (k: key aprm) = v: value aprm {compatible k v}

let key_of (#aprm: app_params) (r: record aprm)
  = let k, _ = r in k

let value_of (#aprm: app_params) (r: record aprm)
  = let _, v = r in v

let to_merkle_value (#aprm: app_params) (v: value aprm { IntV? v })
  = let IntV v = v in
    v
