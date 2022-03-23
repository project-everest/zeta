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

let bit_offset_in_word (i:U16.t { U16.v i < 256 })
  : U32.t & U32.t
  = let open U16 in
    if i <^ 64us
    then 0ul, C.uint16_to_uint32 i
    else if i <^ 128us
    then 1ul, C.uint16_to_uint32 (i -^ 64us)
    else if i <^ 192us
    then 2ul, C.uint16_to_uint32 (i -^ 128us)
    else 3ul, C.uint16_to_uint32 (i -^ 192us)

let nth_63_mod2 (x:U64.t)
  : Lemma (UInt.nth (U64.v x) 63 == (U64.v x % 2 = 1))
  = ()

let ith_bit_64 (x:U64.t) (i:U32.t { U32.v i < 64 })
  : bool
  = U64.shift_right x i `U64.rem` 2uL = 1uL

let ith_bit_64_nth (x:U64.t) (i:U32.t { U32.v i < 64 })
  : Lemma (ith_bit_64 x i == FStar.UInt.nth (U64.v x) (63 - U32.v i))
  = calc (==) {
      FStar.UInt.nth (U64.v (U64.shift_right x i)) 63;
    (==) { FStar.UInt.shift_right_lemma_2 #64 (U64.v x) (U32.v i) 63 }
      UInt.nth #64 (U64.v x) (63 - U32.v i);
    }

let ith_bit (k0:T.base_key) (i:U16.t { U16.v i < 256 })
  : bool
  = let open U16 in
    let kk = k0.T.k in
    let word, bit = bit_offset_in_word i in
    if word = 0ul
    then ith_bit_64 kk.T.v0 bit
    else if word = 1ul
    then ith_bit_64 kk.T.v1 bit
    else if word = 2ul
    then ith_bit_64 kk.T.v2 bit
    else ith_bit_64 kk.T.v3 bit

let set_ith_bit (k0:T.base_key) (i:U16.t { U16.v i < 256 })
  : GTot T.base_key
  = let open U16 in
    let kk = k0.T.k in
    let word, bit = bit_offset_in_word i in
    let mask = U64.shift_left 1uL bit in
    let kk' =
      if word = 0ul
      then { kk with v0 = kk.v0 `U64.logor` mask  }
      else if word = 1ul
      then { kk with v1 = kk.v1 `U64.logor` mask }
      else if word = 2ul
      then { kk with v2 = kk.v2 `U64.logor` mask }
      else { kk with v3 = kk.v3 `U64.logor` mask }
    in
    { k0 with k = kk' }

#push-options "--fuel 0 --ifuel 0"
let set_get_ith_bit_core (k:T.base_key) (i:U16.t { U16.v i < 256 })
  : Lemma ((ith_bit (set_ith_bit k i) i == true))
  = let open U16 in
    let k' = set_ith_bit k i in
    let word, index = bit_offset_in_word i in
    let kk =
      if word = 0ul then k'.k.v0
      else if word = 1ul then k'.k.v1
      else if word = 2ul then k'.k.v2
      else k'.k.v3
    in
    let res = ith_bit_64 kk index in
    let mask = U64.shift_left 1uL index in
      calc (==) {
        ith_bit k' i;
       (==) { }
        ith_bit_64 kk index;
       (==) { ith_bit_64_nth kk index }
        UInt.nth #64 (U64.v kk) (63 - U32.v index);
       (==) {}
        UInt.nth #64 (U64.v (kk `U64.logor` mask)) (63 - U32.v index);
       (==) { UInt.logor_definition #64 (U64.v kk) (U64.v mask) (63 - U32.v index) }
        (UInt.nth #64 (U64.v kk) (63 - U32.v index) ||
         UInt.nth #64 (U64.v mask) (63 - U32.v index));
       (==) { UInt.shift_left_lemma_2 #64 1 (U32.v index) (63 - U32.v index) }
        (UInt.nth #64 (U64.v kk) (63 - U32.v index) ||
         UInt.nth #64 1 63);
       (==) { nth_63_mod2 1uL }
       (UInt.nth #64 (U64.v kk) (63 - U32.v index) ||
        (1%2 = 1));
       (==) {}
        true;
      }
#pop-options

let set_ith_bit_modifies (k:T.base_key)
                         (i:U16.t { U16.v i < 256 })
                         (j:U16.t { U16.v j <> U16.v i /\ U16.v j < 256 })
  : Lemma ((ith_bit (set_ith_bit k i) j == ith_bit k j))
  = admit()

let set_get_ith_bit (k:T.base_key) (i:U16.t { U16.v i < 256 })
  : Lemma ((ith_bit (set_ith_bit k i) i == true) /\
            (forall (j:U16.t { j <> i /\ U16.v j < 256 }). ith_bit (set_ith_bit k i) j == ith_bit k j))
  = set_get_ith_bit_core k i;
    FStar.Classical.forall_intro (set_ith_bit_modifies k i)

let root_base_key: T.base_key =
  let open T in
  {
    k = { v3 = U64.zero; v2 = U64.zero ; v1 = U64.zero ; v0 = U64.zero };
    significant_digits = U16.zero;
  }

let root_key: T.key = InternalKey root_base_key

let ith_bit_root_base_key (i:U16.t { U16.v i < 256 })
  : Lemma (ith_bit root_base_key i == false)
  = let open U16 in
    let res = ith_bit root_base_key i in
    let kk = root_base_key.k in
    let word, bit = bit_offset_in_word i in
    FStar.UInt.shift_right_value_lemma #64 0 (U32.v bit);
    FStar.Math.Lemmas.small_div 0 (pow2 (U32.v bit))

(* if you lift a lowered key, you get the original key, but not the other way round *)
let rec lift_base_key (k: T.base_key)
  : GTot (k':Zeta.Key.base_key {
               Zeta.BinTree.depth k' = U16.v k.significant_digits
          })
    (decreases (U16.v k.significant_digits))
  = let open U16 in
    let open Zeta.BinTree in
    if k.significant_digits = 0us then Root
    else let i = k.significant_digits -^ 1us in
         let k' = lift_base_key ({k with significant_digits = i }) in
         if ith_bit k i
         then RightChild k'
         else LeftChild k'

let rec lower_base_key' (k: Zeta.Key.base_key)
  : GTot (k':T.base_key {
                U16.v k'.significant_digits = Zeta.BinTree.depth k
          })
  = let open Zeta.BinTree in
    match k with
    | Root -> root_base_key

    | LeftChild k ->
      let k' = lower_base_key' k in
      { k' with significant_digits = U16.(k'.significant_digits +^ 1us) }

    | RightChild k ->
      let k' = lower_base_key' k in
      let k'' = { k' with significant_digits = U16.(k'.significant_digits +^ 1us) } in
      set_ith_bit k'' k'.significant_digits


let rec lower_base_key_significant_digits (k: Zeta.Key.base_key)
  : Lemma (let k' = lower_base_key' k in
           U16.v k'.significant_digits = Zeta.BinTree.depth k /\
           (forall (i:U16.t). Zeta.BinTree.depth k <= U16.v i /\
                         U16.v i < 256 ==>
                         ith_bit k' i == false))
  = let open Zeta.BinTree in
    match k with
    | Root ->
      FStar.Classical.forall_intro ith_bit_root_base_key

    | LeftChild k ->
      lower_base_key_significant_digits k

    | RightChild k ->
      lower_base_key_significant_digits k;
      let kk = lower_base_key' k in
      set_get_ith_bit kk kk.significant_digits

#push-options "--query_stats --fuel 2 --ifuel 1 --z3rlimit_factor 4"
let rec lift_lower_id (k:Zeta.Key.base_key)
  : Lemma (lift_base_key (lower_base_key' k) == k)
  = let open U16 in
    let open Zeta.BinTree in
    match k with
    | Root -> ()
    | LeftChild k ->
      lift_lower_id k;
      lower_base_key_significant_digits k
    | RightChild k ->
      lift_lower_id k;
      let k0 = lower_base_key' k in
      assert (lift_base_key k0 == k);
      let res = {set_ith_bit k0 k0.significant_digits with significant_digits = U16.(k0.significant_digits +^ 1us) } in
      set_get_ith_bit k0 k0.significant_digits;
      assert (lower_base_key' (RightChild k) == res)



let lower_base_key (k: Zeta.Key.base_key)
  : GTot (k':T.base_key {
                lift_base_key k' = k
          })
  = lift_lower_id k;
    lower_base_key' k

let desc_dir (k0:T.base_key) (k1:T.base_key { k0 `is_proper_descendent` k1 })
  : bool
  = let open U16 in
    ith_bit k0 k1.T.significant_digits
