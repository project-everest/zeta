module Zeta.Steel.ImplSpecRel

module U16 = FStar.UInt16
module L = FStar.List.Tot
module GK = Zeta.GenKey
module K = Zeta.Key
module AT = Zeta.Steel.ApplicationTypes
module T = Zeta.Steel.FormatsManual
module TSM = Zeta.Steel.ThreadStateModel

let app = AT.aprm

let bv_t = FStar.BitVector.bv_t

let merkle_key = K.merkle_key

val lift_internal_key (k: T.internal_key)
  : K.merkle_key

val lift_key (k: T.key)
  : GK.key app
