module Zeta.GenKey

open Zeta.App
open Zeta.Key
open Zeta.Merkle

module BT = Zeta.BinTree

type key (aprm: app_params) =
  | AppK: k: app_key aprm.adm -> key aprm
  | IntK: k: merkle_key -> key aprm

let to_base_key #aprm (k: key aprm): base_key
  = match k with
    | AppK k -> aprm.keyhashfn k
    | IntK k -> k

let lemma_key_type (#app:_) (gk: key app)
  : Lemma (ensures (is_merkle_key (to_base_key gk) = IntK? gk))
          [SMTPat (to_base_key gk)]
  = ()
