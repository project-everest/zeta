module Zeta.Record

open FStar.BitVector
open Zeta.App
open Zeta.BinTree
open Zeta.Hash
open Zeta.Key

(* information about a desc stored in a merkle node *)
type desc_hash = 
  | Empty: desc_hash
  | Desc: k:key -> h:hash_value -> b:bool -> desc_hash

(* merkle value: information about left and right descendants *)
type merkle_value = 
  | MkValue: l:desc_hash -> r:desc_hash -> merkle_value

let desc_hash_dir (v:merkle_value) (d:bin_tree_dir) = 
  match d with
  | Left -> MkValue?.l v
  | Right -> MkValue?.r v

let merkle_record = merkle_key & merkle_value

let mv_points_to_none (v: merkle_value) (d:bin_tree_dir): bool =
  desc_hash_dir v d = Empty

let mv_points_to_some (v:merkle_value) (d:bin_tree_dir): bool = 
  Desc? (desc_hash_dir v d) 

let mv_pointed_key (v:merkle_value) (d:bin_tree_dir{mv_points_to_some v d}): key = 
  Desc?.k (desc_hash_dir v d)

let mv_pointed_hash (v:merkle_value) (d:bin_tree_dir{mv_points_to_some v d}): hash_value = 
  Desc?.h (desc_hash_dir v d)

let mv_points_to (v:merkle_value) (d:bin_tree_dir) (k:key): bool = 
  mv_points_to_some v d && mv_pointed_key v d = k

let mv_evicted_to_blum (v:merkle_value) (d:bin_tree_dir {mv_points_to_some v d}): bool =
  Desc?.b (desc_hash_dir v d)

(* a record is a union of merkle (internal) record and app record *)
type record (aprm: app_params) =
  | App: r: app_record aprm.adm -> record aprm
  | Int: r: merkle_record -> record aprm

let value_t (#aprm: app_params) (r: record aprm): eqtype =
  match r with
  | App _ -> app_value_nullable aprm.adm
  | Int _ -> merkle_value

let update (#aprm: app_params) (r: record aprm) (v: value_t r) =
  match r with
  | App (k,_) -> App (k,v)
  | Int (k,_) -> Int (k,v)
