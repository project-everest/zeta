module Zeta.Steel.ImplSpecRel

module U16 = FStar.UInt16
module L = FStar.List.Tot
module GK = Zeta.GenKey
module K = Zeta.Key
module AT = Zeta.Steel.ApplicationTypes
module T = Zeta.Steel.FormatsManual
module TSM = Zeta.Steel.ThreadStateModel
module M = Zeta.Merkle

let app = AT.aprm

let bv_t = FStar.BitVector.bv_t

let merkle_key = K.merkle_key

val lift_internal_key (k: T.internal_key)
  : K.merkle_key

let lift_key (k: T.key)
  : GK.key app
  = let open T in
    let open GK in
    match k with
    | InternalKey k -> IntK (lift_internal_key k)
    | ApplicationKey k -> AppK k

(* application keys can be invertibly lifted and lowered *)
let lower_app_key (k: GK.key app {GK.AppK? k})
  : T.key
  = let open T in
    let open GK in
    match k with
    | AppK k -> ApplicationKey k

let related_internal_key (sk: T.internal_key) (ik: K.merkle_key)
  = ik = lift_internal_key sk

let related_key (sk: T.key) (ik: GK.key app)
  = ik = lift_key sk

let related_desc_hash (s_hash: T.descendent_hash)
                      (i_hash: M.desc_hash_t)
  = let open T in
    let open M in
    match s_hash, i_hash with
    | Dh_vnone (), Empty -> True
    | Dh_vsome dhd, Desc k h b -> admit()
    | _ -> False
