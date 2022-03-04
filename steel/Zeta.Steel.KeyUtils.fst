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

assume
val lift_base_key (k: T.base_key)
  : GTot (k':Zeta.Key.base_key { Zeta.BinTree.depth k' = U16.v k.significant_digits })


let root_base_key: T.base_key =
  let open T in
  {
    k = { v3 = U64.zero; v2 = U64.zero ; v1 = U64.zero ; v0 = U64.zero };
    significant_digits = U16.zero;
  }

let root_key: T.key = InternalKey root_base_key

(* if you lift a lowered key, you get the original key, but not the other way round *)
#push-options "--query_stats"
assume
val shift_left_256 (i:u256) (n:U16.t { U16.v n < 256 })
  : u256
let shift_left_key (k:T.base_key { U16.v k.significant_digits < 256 })
  : T.base_key
  = let key = shift_left_256 k.k 1us in
    { k with k=key; significant_digits = U16.(k.significant_digits +^ 1us) }

assume
val shift_left_256_lemma (k:T.base_key { U16.v k.significant_digits < 256 })
  : Lemma ((forall (i:U16.t { U16.v i < 255 }).
              ith_bit k i == ith_bit (shift_left_key k) U16.(i +^ 1us)) /\
            ith_bit (shift_left_key k) 0us = false)

let rec lift_base_key' (k: T.base_key)
  : GTot (k':Zeta.Key.base_key {
               Zeta.BinTree.depth k' = U16.v k.significant_digits
          })
    (decreases (U16.v k.significant_digits))
  = let open U16 in
    let open Zeta.BinTree in
    if k.significant_digits = 0us then Root
    else let i = k.significant_digits -^ 1us in
         let k' = lift_base_key' ({k with significant_digits = i }) in
         if ith_bit k i
         then RightChild k'
         else LeftChild k'

let rec lower_base_key' (k: Zeta.Key.base_key)
  : GTot (k':T.base_key {
       //        lift_base_key k' = k /\
                U16.v k'.significant_digits = Zeta.BinTree.depth k
          })
  = let open Zeta.BinTree in
    match k with
    | Root -> root_base_key
    | LeftChild k -> shift_left_key (lower_base_key' k)
    | RightChild k ->
      let k = shift_left_key (lower_base_key' k) in
      let key = {k.k with v0 = k.k.v0 `U64.logxor` 1uL} in
      {k with k = key }

let rec lift_lower_id (k:Zeta.Key.base_key)
  : Lemma (lift_base_key' (lower_base_key' k) == k)
  = let open U16 in
    let open Zeta.BinTree in
    match k with
    | Root -> ()
    | LeftChild k ->
      lift_lower_id k;
      let k0 = lower_base_key' k in
      let i = k0.significant_digits in
      shift_left_256_lemma k0;
      assume (ith_bit k0 i = false);
      admit()
    | _ -> admit()

assume
val lower_base_key (k: Zeta.Key.base_key)
  : GTot (k':T.base_key {
                lift_base_key k' = k
          })

let desc_dir (k0:T.base_key) (k1:T.base_key { k0 `is_proper_descendent` k1 })
  : bool
  = let open U16 in
    ith_bit k0 k1.T.significant_digits
