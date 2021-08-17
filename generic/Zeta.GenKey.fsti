module Zeta.GenKey

open Zeta.App
open Zeta.Key
open Zeta.Merkle

module BT = Zeta.BinTree

type key (aprm: app_params) =
  | AppK: k: app_key aprm.adm -> key aprm
  | IntK: k: Merkle.key -> key aprm

(* extend proper desc relationship to general keys *)
let is_proper_desc #aprm (kd: key aprm) (ka: key aprm)
  = match kd, ka with
    | _, AppK _ -> false (* nothing is a proper descendant of an application key *)
    | AppK kd, IntK ka ->
      let kd: leaf_key = aprm.keyhashfn kd in
      BT.is_proper_desc kd ka
    | IntK kd, IntK ka ->
      BT.is_proper_desc kd ka

let desc_dir #aprm (kd: key aprm) (ka: key aprm { is_proper_desc kd ka })
  = match kd, ka with
    | AppK kd, IntK ka ->
      let kd = aprm.keyhashfn kd in
      BT.desc_dir kd ka
    | IntK kd, IntK ka ->
      BT.desc_dir kd ka
