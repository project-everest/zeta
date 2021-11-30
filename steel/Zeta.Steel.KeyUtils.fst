module Zeta.Steel.KeyUtils
open FStar.Ghost
open Zeta.Steel.ApplicationTypes
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
open Zeta.Steel.FormatsManual
module T = Zeta.Steel.FormatsManual
module C = FStar.Int.Cast

let shift_right_64 (x:U64.t) (w:U16.t{U16.v w <= 64})
  : U64.t
  = if w = 64us then 0uL
    else U64.shift_right x (C.uint16_to_uint32 w)

let truncate_key (k:T.base_key)
                 (w:U16.t { U16.v w < U16.v k.T.significant_digits })
  : T.base_key
  = let open U16 in
    let kk =
      let kk = k.T.k in
      let zkey = { T.v0 = 0uL; T.v1 = 0uL; T.v2 = 0uL; T.v3 = 0uL } in
      if w <=^ 64us
      then { zkey with T.v0 = shift_right_64 kk.T.v0 (64us -^ w) }
      else if w <=^ 128us
      then { zkey with T.v0 = kk.T.v0;
                       T.v1 = shift_right_64 kk.T.v1 (128us -^ w) }
      else if w <^ 192us
      then { kk with T.v2 = shift_right_64 kk.T.v2 (192us -^ w); T.v3 = 0uL }
      else { kk with T.v3 = shift_right_64 kk.T.v3 (256us -^ w) }
    in
    { k with T.k = kk; T.significant_digits = w }

let is_proper_descendent (k0 k1:T.base_key)
  : bool
  = let open FStar.UInt16 in
    k0.T.significant_digits >^ k1.T.significant_digits &&
    truncate_key k0 k1.T.significant_digits = k1

let is_proper_descendent_key_type (k0 k1:T.internal_key)
  : Lemma
    (requires is_proper_descendent k0 k1)
    (ensures  not (T.is_internal_key_for_data k1))
    [SMTPat (is_proper_descendent k0 k1)]
  = ()

let ith_bit (k0:T.base_key) (i:U16.t { U16.v i < 256 })
  : bool
  = let open U16 in
    let kk = k0.T.k in
    if i <^ 64us
    then (U64.shift_right kk.T.v0 (C.uint16_to_uint32 i)) `U64.rem` 2uL = 1uL
    else if i <^ 128us
    then (U64.shift_right kk.T.v1 (C.uint16_to_uint32 (i -^ 64us))) `U64.rem` 2uL = 1uL
    else if i <^ 192us
    then (U64.shift_right kk.T.v2 (C.uint16_to_uint32 (i -^ 128us))) `U64.rem` 2uL = 1uL
    else (U64.shift_right kk.T.v3 (C.uint16_to_uint32 (i -^ 192us))) `U64.rem` 2uL = 1uL

let lift_base_key (k: T.base_key)
  : Zeta.Key.base_key
  = admit()

(* if you lift a lowered key, you get the original key, but not the other way round *)
let lower_base_key (k: Zeta.Key.base_key)
  : k':T.base_key { lift_base_key k' = k }
  = admit()

let desc_dir (k0:T.base_key) (k1:T.base_key { k0 `is_proper_descendent` k1 })
  : bool
  = let open U16 in
    ith_bit k0 k1.T.significant_digits
