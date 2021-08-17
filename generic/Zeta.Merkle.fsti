module Zeta.Merkle

open Zeta.BinTree
open Zeta.Hash
open Zeta.Key

(* information about a desc stored in a merkle node *)
type desc_hash_t =
  | Empty: desc_hash_t
  | Desc: k:base_key -> h:hash_value -> b:bool -> desc_hash_t

(* merkle value: information about left and right descendants *)
type value = {
  left: desc_hash_t;
  right: desc_hash_t;
}

let desc_hash (v:value) (d:bin_tree_dir) =
  match d with
  | Left -> v.left
  | Right -> v.right

let points_to_none (d:bin_tree_dir) (v: value) : bool =
  desc_hash v d = Empty

let points_to_some (v:value) (d:bin_tree_dir): bool =
  Desc? (desc_hash v d)

let pointed_key (v:value) (d:bin_tree_dir{points_to_some v d}): base_key =
  Desc?.k (desc_hash v d)

let pointed_hash (v:value) (d:bin_tree_dir{points_to_some v d}): hash_value =
  Desc?.h (desc_hash v d)

let points_to (v:value) (d:bin_tree_dir) (k:base_key): bool =
  points_to_some v d && pointed_key v d = k

let evicted_to_blum (v:value) (d:bin_tree_dir {points_to_some v d}): bool =
  Desc?.b (desc_hash v d)

let update_value (v: value) (d: bin_tree_dir) (k:base_key) (h:hash_value) (b:bool)
  = match d with
    | Left -> { left = Desc k h b; right = v.right; }
    | Right -> { left = v.left; right = Desc k h b; }
