module Zeta.Steel.KeyUtils
open FStar.Ghost
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module C = FStar.Int.Cast

let significant_digits_t =
  significant_digits: U16.t { U16.v significant_digits <= 256 }

type raw_key = {
  k: u256;
  significant_digits : significant_digits_t;
}

inline_for_extraction
let root_raw_key: raw_key =
  {
    k = { v3 = 0uL; v2 = 0uL ; v1 = 0uL ; v0 = 0uL };
    significant_digits = 0us;
  }

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

let truncate_word (k:U64.t) (index:U32.t { U32.v index < 64 })
  : U64.t
  = if index = 0ul then 0uL
    else let shift_index = U32.(64ul -^ index) in
         let mask = U64.shift_right 0xffffffffffffffffuL shift_index in
         U64.logand k mask

let truncate_key (k:raw_key)
                 (w:U16.t { U16.v w <= U16.v k.significant_digits })
  : raw_key
  = let open U16 in
    if w = 256us then k //w = k.significant_digits then k
    else (
      let word, index = bit_offset_in_word w in
      let kk = k.k in
      let kk' =
        if word = 0ul
        then { kk with v0 = truncate_word kk.v0 index; v1=0uL; v2=0uL; v3=0uL}
        else if word = 1ul
        then { kk with v1 = truncate_word kk.v1 index; v2=0uL; v3=0uL}
        else if word = 2ul
        then { kk with v2 = truncate_word kk.v2 index; v3=0uL}
        else { kk with v3 = truncate_word kk.v3 index }
      in
      { k = kk'; significant_digits = w }
    )

let is_proper_descendent' (k0 k1:raw_key)
  : bool
  = let open FStar.UInt16 in
    k0.significant_digits >^ k1.significant_digits &&
    truncate_key k0 k1.significant_digits = k1

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

let ith_bit_64_extensional (x y:U64.t)
  : Lemma
    (requires (forall (i:U32.t { U32.v i < 64 }). ith_bit_64 x i == ith_bit_64 y i))
    (ensures x == y)
  = introduce forall (i:nat { i < 64 }). UInt.nth (U64.v x) i == UInt.nth (U64.v y) i
    with (
      ith_bit_64_nth x (U32.uint_to_t (63 - i));
      ith_bit_64_nth y (U32.uint_to_t (63 - i))
    );
    UInt.nth_lemma #64 (U64.v x) (U64.v y)

let ith_bit (k0:raw_key) (i:U16.t { U16.v i < 256 })
  : bool
  = let open U16 in
    let kk = k0.k in
    let word, bit = bit_offset_in_word i in
    if word = 0ul
    then ith_bit_64 kk.v0 bit
    else if word = 1ul
    then ith_bit_64 kk.v1 bit
    else if word = 2ul
    then ith_bit_64 kk.v2 bit
    else ith_bit_64 kk.v3 bit

#push-options "--fuel 0 --ifuel 0"
let ith_bit_extensional (x y:raw_key)
  : Lemma
    (requires
      x.significant_digits == y.significant_digits /\
      (forall (i:U16.t { U16.v i < 256 }). ith_bit x i == ith_bit y i))
    (ensures x == y)
  = introduce forall (i:U32.t{U32.v i < 64}). ith_bit_64 x.k.v0 i == ith_bit_64 y.k.v0 i
    with (
      assert (ith_bit_64 x.k.v0 i == ith_bit x (U16.uint_to_t (U32.v i)));
      assert (ith_bit_64 y.k.v0 i == ith_bit y (U16.uint_to_t (U32.v i)))
    );
    ith_bit_64_extensional x.k.v0 y.k.v0;
    introduce forall (i:U32.t{U32.v i < 64}). ith_bit_64 x.k.v1 i == ith_bit_64 y.k.v1 i
    with (
      assert (ith_bit_64 x.k.v1 i == ith_bit x (U16.uint_to_t (64 + U32.v i)));
      assert (ith_bit_64 y.k.v1 i == ith_bit y (U16.uint_to_t (64 + U32.v i)))
    );
    ith_bit_64_extensional x.k.v1 y.k.v1;
    introduce forall (i:U32.t{U32.v i < 64}). ith_bit_64 x.k.v2 i == ith_bit_64 y.k.v2 i
    with (
      assert (ith_bit_64 x.k.v2 i == ith_bit x (U16.uint_to_t (128 + U32.v i)));
      assert (ith_bit_64 y.k.v2 i == ith_bit y (U16.uint_to_t (128 + U32.v i)))
    );
    ith_bit_64_extensional x.k.v2 y.k.v2;
    introduce forall (i:U32.t{U32.v i < 64}). ith_bit_64 x.k.v3 i == ith_bit_64 y.k.v3 i
    with (
      assert (ith_bit_64 x.k.v3 i == ith_bit x (U16.uint_to_t (192 + U32.v i)));
      assert (ith_bit_64 y.k.v3 i == ith_bit y (U16.uint_to_t (192 + U32.v i)))
    );
    ith_bit_64_extensional x.k.v3 y.k.v3
#pop-options

let set_ith_bit (k0:raw_key) (i:U16.t { U16.v i < 256 })
  : GTot raw_key
  = let open U16 in
    let kk = k0.k in
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

let clear_ith_bit_64 (k:U64.t) (i:U32.t { U32.v i < 64 })
  : GTot U64.t
  = let v = UInt.to_vec #64 (U64.v k) in
    let index = 63 - U32.v i in
    let v' = Seq.upd v index false in
    U64.uint_to_t (UInt.from_vec #64 v')

let clear_ith_bit (k0:raw_key) (i:U16.t { U16.v i < 256 })
  : GTot raw_key
  = let open U16 in
    let kk = k0.k in
    let word, bit = bit_offset_in_word i in
    let kk' =
      if word = 0ul
      then { kk with v0 = clear_ith_bit_64 kk.v0 bit }
      else if word = 1ul
      then { kk with v1 = clear_ith_bit_64 kk.v1 bit }
      else if word = 2ul
      then { kk with v2 = clear_ith_bit_64 kk.v2 bit }
      else { kk with v3 = clear_ith_bit_64 kk.v3 bit }
    in
    { k0 with k = kk' }

#push-options "--fuel 0 --ifuel 0"

let set_get_ith_bit_core (k:raw_key) (i:U16.t { U16.v i < 256 })
  : Lemma ((ith_bit (set_ith_bit k i) i == true))
  = let open U16 in
    let k' = set_ith_bit k i in
    let word, index = bit_offset_in_word i in
    let kk, kk' =
      if word = 0ul then k.k.v0, k'.k.v0
      else if word = 1ul then k.k.v1, k'.k.v1
      else if word = 2ul then k.k.v2, k'.k.v2
      else k.k.v3, k'.k.v3
    in
    let res = ith_bit_64 kk' index in
    let mask = U64.shift_left 1uL index in
      calc (==) {
        ith_bit k' i;
       (==) { }
        ith_bit_64 kk' index;
       (==) { ith_bit_64_nth kk' index }
        UInt.nth #64 (U64.v kk') (63 - U32.v index);
       (==) { }
        UInt.nth #64 (U64.v (kk `U64.logor` mask)) (63 - U32.v index);
       (==) { UInt.logor_definition #64 (U64.v kk') (U64.v mask) (63 - U32.v index) }
        (UInt.nth #64 (U64.v kk) (63 - U32.v index) ||
         UInt.nth #64 (U64.v mask) (63 - U32.v index));
       (==) { UInt.shift_left_lemma_2 #64 1 (U32.v index) (63 - U32.v index) }
        (UInt.nth #64 (U64.v kk') (63 - U32.v index) ||
         UInt.nth #64 1 63);
       (==) { nth_63_mod2 1uL }
       (UInt.nth #64 (U64.v kk') (63 - U32.v index) ||
        (1%2 = 1));
       (==) {}
        true;
      }

let set_ith_bit_modifies (k:raw_key)
                         (i:U16.t { U16.v i < 256 })
                         (j:U16.t { U16.v j <> U16.v i /\ U16.v j < 256 })
  : Lemma ((ith_bit (set_ith_bit k i) j == ith_bit k j))
  = let open U16 in
    let k' = set_ith_bit k i in
    let word_i, index_i = bit_offset_in_word i in
    let word, index = bit_offset_in_word j in
    if word_i <> word
    then ()
    else (
      assert (index_i <> index);
      let kk, kk' =
        if word = 0ul then k.k.v0, k'.k.v0
        else if word = 1ul then k.k.v1, k'.k.v1
        else if word = 2ul then k.k.v2, k'.k.v2
        else k.k.v3, k'.k.v3
      in
      let res = ith_bit_64 kk' index in
      let mask = U64.shift_left 1uL index_i in
      calc (==) {
        ith_bit k' j;
       (==) { }
        ith_bit_64 kk' index;
       (==) { ith_bit_64_nth kk' index }
        UInt.nth #64 (U64.v kk') (63 - U32.v index);
       (==) {}
        UInt.nth #64 (U64.v (kk `U64.logor` mask)) (63 - U32.v index);
       (==) { UInt.logor_definition #64 (U64.v kk) (U64.v mask) (63 - U32.v index) }
        (UInt.nth #64 (U64.v kk) (63 - U32.v index) ||
         UInt.nth #64 (U64.v mask) (63 - U32.v index));
       (==) {
              if U32.v index < U32.v index_i
              then (
                calc (==) {
                  UInt.nth #64 (U64.v mask) (63 - U32.v index);
                (==) { UInt.shift_left_lemma_1 #64 1 (U32.v index_i) (63 - U32.v index) }
                  false;
                }
              ) else (
                calc (==) {
                  UInt.nth #64 (U64.v mask) (63 - U32.v index);
                (==) { UInt.shift_left_lemma_2 #64 1 (U32.v index_i) (63 - U32.v index) }
                  UInt.nth #64 1 (63 - U32.v index + U32.v index_i);
                (==) { UInt.one_nth_lemma #64 (63 - U32.v index + U32.v index_i) }
                  false;
                }
              )
            }
         UInt.nth #64 (U64.v kk) (63 - U32.v index);
       (==) { ith_bit_64_nth kk index }
        ith_bit_64 kk index;
       (==) { }
        ith_bit k j;
      }
    )

let clear_ith_bit_64_spec (k:U64.t) (i:U32.t { U32.v i < 64 })
  : Lemma (ith_bit_64 (clear_ith_bit_64 k i) i == false /\
           (forall j.
             j <> i ==>
             ith_bit_64 (clear_ith_bit_64 k i) j ==
             ith_bit_64 k j))
  = FStar.Classical.forall_intro (ith_bit_64_nth (clear_ith_bit_64 k i));
    FStar.Classical.forall_intro (ith_bit_64_nth k)

let clear_get_ith_bit_core (k:raw_key) (i:U16.t { U16.v i < 256 })
  : Lemma (ith_bit (clear_ith_bit k i) i == false)
  = FStar.Classical.forall_intro_2 clear_ith_bit_64_spec

let clear_ith_bit_modifies (k:raw_key)
                         (i:U16.t { U16.v i < 256 })
                         (j:U16.t { U16.v j <> U16.v i /\ U16.v j < 256 })
  : Lemma (ith_bit (clear_ith_bit k i) j == ith_bit k j)
  = FStar.Classical.forall_intro_2 clear_ith_bit_64_spec

#pop-options

let set_get_ith_bit (k:raw_key) (i:U16.t { U16.v i < 256 })
  : Lemma ((ith_bit (set_ith_bit k i) i == true) /\
            (forall (j:U16.t { j <> i /\ U16.v j < 256 }). ith_bit (set_ith_bit k i) j == ith_bit k j))
  = set_get_ith_bit_core k i;
    FStar.Classical.forall_intro (set_ith_bit_modifies k i)

let clear_set_ith_bit (k:raw_key) (i:U16.t { U16.v i < 256 })
  : Lemma (clear_ith_bit (set_ith_bit k i) i ==
           clear_ith_bit k i)
  = FStar.Classical.forall_intro_2 clear_get_ith_bit_core;
    FStar.Classical.forall_intro_3 clear_ith_bit_modifies;
    FStar.Classical.forall_intro_2 set_get_ith_bit;
    ith_bit_extensional (clear_ith_bit (set_ith_bit k i) i)
                        (clear_ith_bit k i)

let clear_ith_bit_elim (k:raw_key) (i:U16.t { U16.v i < 256 })
  : Lemma (requires ith_bit k i = false)
          (ensures clear_ith_bit k i == k)
  = FStar.Classical.forall_intro_2 clear_get_ith_bit_core;
    FStar.Classical.forall_intro_3 clear_ith_bit_modifies;
    ith_bit_extensional (clear_ith_bit k i) k

let ith_bit_root_raw_key (i:U16.t { U16.v i < 256 })
  : Lemma (ith_bit root_raw_key i == false)
  = let open U16 in
    let res = ith_bit root_raw_key i in
    let kk = root_raw_key.k in
    let word, bit = bit_offset_in_word i in
    FStar.UInt.shift_right_value_lemma #64 0 (U32.v bit);
    FStar.Math.Lemmas.small_div 0 (pow2 (U32.v bit))

(* if you lift a lowered key, you get the original key, but not the other way round *)
let rec lift_raw_key (k: raw_key)
  : GTot (k':Zeta.Key.base_key {
               Zeta.BinTree.depth k' = U16.v k.significant_digits
          })
    (decreases (U16.v k.significant_digits))
  = let open U16 in
    let open Zeta.BinTree in
    if k.significant_digits = 0us then Root
    else let i = k.significant_digits -^ 1us in
         let k' = lift_raw_key ({k with significant_digits = i }) in
         if ith_bit k i
         then RightChild k'
         else LeftChild k'

let rec lower_base_key' (k: Zeta.Key.base_key)
  : GTot (k':raw_key {
                U16.v k'.significant_digits = Zeta.BinTree.depth k
          })
  = let open Zeta.BinTree in
    match k with
    | Root -> root_raw_key

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
      FStar.Classical.forall_intro ith_bit_root_raw_key

    | LeftChild k ->
      lower_base_key_significant_digits k

    | RightChild k ->
      lower_base_key_significant_digits k;
      let kk = lower_base_key' k in
      set_get_ith_bit kk kk.significant_digits

let rec lift_raw_key_irrelevant_bits (b0 b1:raw_key)
  : Lemma
    (requires b0.significant_digits = b1.significant_digits /\
              (forall (i:U16.t{U16.v i < U16.v b0.significant_digits}).{:pattern (has_type i U16.t)} ith_bit b0 i == ith_bit b1 i))
    (ensures  lift_raw_key b0 == lift_raw_key b1)
    (decreases U16.v b0.significant_digits)
  = if b0.significant_digits = 0us then ()
    else (
      let b0' = { b0 with significant_digits = U16.(b0.significant_digits -^ 1us) } in
      let b1' = { b1 with significant_digits = U16.(b1.significant_digits -^ 1us) } in
      lift_raw_key_irrelevant_bits b0' b1'
    )

let rec lift_lower_id (k:Zeta.Key.base_key)
  : Lemma (lift_raw_key (lower_base_key' k) == k)
  = let open U16 in
    let open Zeta.BinTree in
    match k with
    | Root -> ()
    | LeftChild k' ->
      lift_lower_id k';
      lower_base_key_significant_digits k'
    | RightChild k' ->
      lift_lower_id k';
      lower_base_key_significant_digits k';
      let k0' = lower_base_key' k' in
      assert (lift_raw_key k0' == k');
      set_get_ith_bit k0' k0'.significant_digits;
      let k0 = lower_base_key' k in
      assert (ith_bit k0 k0'.significant_digits);
      assert (k0.significant_digits <> 0us);
      calc (==) {
          lift_raw_key k0;
      (==) {}
          RightChild (lift_raw_key ({k0 with significant_digits = k0.significant_digits -^ 1us }));
      (==) { lift_raw_key_irrelevant_bits k0' ({k0 with significant_digits = k0.significant_digits -^ 1us }) }
          RightChild (lift_raw_key k0');
      }

let lower_base_key_raw (k: Zeta.Key.base_key)
  : GTot (k':raw_key {
                lift_raw_key k' = k
          })
  = lift_lower_id k;
    lower_base_key' k

let desc_dir_raw (k0:raw_key) (k1:raw_key { k0 `is_proper_descendent'` k1 })
  : bool
  = let open U16 in
    not (ith_bit k0 k1.significant_digits)

let parent (k:raw_key { k.significant_digits <> 0us })
  : GTot raw_key
  = let i = U16.(k.significant_digits -^ 1us) in
    if ith_bit k i
    then { clear_ith_bit k i with significant_digits = i }
    else { k with significant_digits = i }

#push-options "--query_stats --fuel 1 --ifuel 0 --z3rlimit_factor 10"
let is_parent_related (k:raw_key { k.significant_digits <> 0us })
                      (ik:Zeta.Key.base_key)
  : Lemma
    (requires k == lower_base_key_raw ik)
    (ensures parent k == lower_base_key_raw (Zeta.BinTree.parent ik))
  = let open U16 in
    match ik with
    | Zeta.BinTree.LeftChild ik' ->
      let sk' = lower_base_key_raw ik' in
      calc (==) {
        lower_base_key_raw (Zeta.BinTree.parent ik);
       (==) {}
        lower_base_key_raw ik';
       (==) {}
        { lower_base_key_raw ik with significant_digits = sk'.significant_digits };
       (==) { }
        parent k;
      }
    | Zeta.BinTree.RightChild ik' ->
      let sk' = lower_base_key_raw ik' in
      assert (Zeta.BinTree.parent ik == ik');
      calc (==) {
        lower_base_key' (Zeta.BinTree.parent ik);
       (==) { }
        lower_base_key' ik';
       (==) { lower_base_key_significant_digits ik';
              clear_ith_bit_elim (lower_base_key' ik') sk'.significant_digits }
        clear_ith_bit (lower_base_key' ik') sk'.significant_digits;
       (==) { }
        clear_ith_bit ({ lower_base_key' ik' with significant_digits = sk'.significant_digits }) sk'.significant_digits;
       (==) { clear_set_ith_bit ({ lower_base_key' ik' with significant_digits = sk'.significant_digits }) sk'.significant_digits }
        clear_ith_bit
          (set_ith_bit ({ lower_base_key' ik' with significant_digits = sk'.significant_digits }) sk'.significant_digits)
          sk'.significant_digits;
       (==) { }
        clear_ith_bit ({ lower_base_key' ik with significant_digits = sk'.significant_digits }) sk'.significant_digits;
       (==) { }
        parent k;
      }

let rec is_desc_raw (k0 k1:raw_key)
  : GTot bool (decreases (U16.v (k0.significant_digits)))
  = if k0 = k1
    then true
    else if k0.significant_digits = 0us
    then false
    else is_desc_raw (parent k0) k1

let rec is_desc_raw_related (k0 k1:raw_key) (ik0 ik1:Zeta.Key.base_key)
  : Lemma
    (requires
      k0 == lower_base_key_raw ik0 /\
      k1 == lower_base_key_raw ik1)
    (ensures
      is_desc_raw k0 k1 == Zeta.BinTree.is_desc_aux ik0 ik1)
    (decreases (U16.v k0.significant_digits))
  = if k0 = k1 then ()
    else if k0.significant_digits = 0us then (
      lift_lower_id Zeta.BinTree.Root
    )
    else (
      is_parent_related k0 ik0;
      is_desc_raw_related (parent k0) k1 (Zeta.BinTree.parent ik0) ik1
    )

let rec truncate_key_spec (k:raw_key)
                          (w:U16.t{U16.v w <= U16.v k.significant_digits })
  : GTot (k':raw_key {k'.significant_digits == w})
         (decreases (U16.v k.significant_digits))
  = if k.significant_digits = w then k
    else truncate_key_spec (parent k) w

let rec truncate_key_spec_ith_bit (k:raw_key)
                                  (w:U16.t{U16.v w <= U16.v k.significant_digits })
  : Lemma
    (ensures (
      let k' = truncate_key_spec k w in
      k'.significant_digits == w /\
      (forall (i:U16.t { U16.v i < 256 }).
         if U16.v w <= U16.v i &&
            U16.v i < U16.v k.significant_digits
         then ith_bit k' i == false
         else ith_bit k' i == ith_bit k i)))
    (decreases (U16.v k.significant_digits))
  = if k.significant_digits = w then ()
    else (
      truncate_key_spec_ith_bit (parent k) w;
      clear_get_ith_bit_core k U16.(k.significant_digits -^ 1us);
      Classical.forall_intro (clear_ith_bit_modifies k U16.(k.significant_digits -^ 1us))
    )

let ith_bit_zero ()
  : Lemma (forall (i:U32.t { U32.v i < 64 }). ith_bit_64 0uL i == false)
  = introduce forall (i:U32.t { U32.v i < 64 }). ith_bit_64 0uL i == false
    with (
      ith_bit_64_nth 0uL i;
      FStar.UInt.zero_nth_lemma #64 (63 - U32.v i)
    )

#push-options "--fuel 0"
let truncate_word_ith_bit (k:U64.t)
                          (w:U32.t { U32.v w < 64 })
                          (i:U32.t { U32.v i < 64 })
  : Lemma
    (ensures (
      let k' = truncate_word k w in
      if U32.v i < U32.v w
      then ith_bit_64 k' i == ith_bit_64 k i
      else ith_bit_64 k' i == false))
  = if w = 0ul then (
       ith_bit_zero ()
    )
    else (
      let index = U32.(64ul -^ w) in
      let mask = 0xffffffffffffffffuL `U64.shift_right` index in
      let k' = U64.logand k mask in
      ith_bit_64_nth k i;
      calc (==) {
        ith_bit_64 k' i;
       (==) { ith_bit_64_nth k' i }
        UInt.nth #64 (U64.v k') (63 - U32.v i);
       (==) { UInt.logand_definition #64 (U64.v k) (U64.v mask) (63 - U32.v i) }
        (UInt.nth #64 (U64.v k) (63 - U32.v i) &&
         UInt.nth #64 (U64.v mask) (63 - U32.v i));
      };
      if U32.v i < U32.v w
      then (
        UInt.shift_right_lemma_2 #64 (UInt.ones 64) (U32.v index) (63 - U32.v i)
      )
      else (
        UInt.shift_right_lemma_1 #64 (UInt.ones 64) (U32.v index) (63 - U32.v i)
      )
    )
#pop-options

#push-options "--fuel 0 --ifuel 1"
let truncate_key_ith_bit (k:raw_key)
                         (w:U16.t{U16.v w <= U16.v k.significant_digits })
  : Lemma
    (ensures (
      let k' = truncate_key k w in
      // if w = k.significant_digits then k' = k
      // else
  (
        k'.significant_digits == w /\
        (forall (i:U16.t { U16.v i < 256 }).
          if U16.v i < U16.v w
          then ith_bit k' i == ith_bit k i
          else ith_bit k' i == false))))
  = if w = 256us then ()
    else (
      let k' = truncate_key k w in
      let w32 = U32.uint_to_t (U16.v w) in
      introduce forall (i:U16.t { U16.v i < 256 }).
                  if U16.v i < U16.v w
                  then (ith_bit k' i == ith_bit k i)
                  else (ith_bit k' i == false)
      with (
        ith_bit_zero ();
        let i32 = U32.uint_to_t (U16.v i) in
        if U16.v w < 64
        then (
          if U16.v i < 64
          then truncate_word_ith_bit k.k.v0 w32 i32
        )
        else if U16.v w < 128
        then (
          if 64 <= U16.v i && U16.v i < 128
          then truncate_word_ith_bit k.k.v1 U32.(w32 -^ 64ul) U32.(i32 -^ 64ul)
        )
        else if U16.v w < 192
        then (
          if 128 <= U16.v i && U16.v i < 192
          then truncate_word_ith_bit k.k.v2 U32.(w32 -^ 128ul) U32.(i32 -^ 128ul)
        )
        else (
          if 192 <= U16.v i
          then truncate_word_ith_bit k.k.v3 U32.(w32 -^ 192ul) U32.(i32 -^ 192ul)
        )
      )
    )
#pop-options

let good_raw_key (k:raw_key)
  = forall (i:U16.t { U16.v i < 256 && U16.v i >= U16.v k.significant_digits }). ith_bit k i = false

let truncate_key_correct (k:raw_key) (w:U16.t { U16.v w <= U16.v k.significant_digits })
  : Lemma
    (requires good_raw_key k)
    (ensures truncate_key k w == truncate_key_spec k w)
  = truncate_key_ith_bit k w;
    truncate_key_spec_ith_bit k w;
    ith_bit_extensional (truncate_key k w) (truncate_key_spec k w)

let rec is_desc_significant_digits (k0 k1:raw_key)
  : Lemma
    (requires is_desc_raw k0 k1)
    (ensures (U16.v k0.significant_digits >= U16.v k1.significant_digits /\
             (U16.v k0.significant_digits = U16.v k1.significant_digits  ==> k0 == k1)))
    (decreases U16.v k0.significant_digits)
  = if k0 = k1 then ()
    else is_desc_significant_digits (parent k0) k1

let rec is_desc_truncate_key_spec (k0 k1:raw_key)
  : Lemma
    (requires U16.v k0.significant_digits >= U16.v k1.significant_digits)
    (ensures is_desc_raw k0 k1 == (truncate_key_spec k0 k1.significant_digits = k1))
    (decreases (U16.v k0.significant_digits))
  = if k0 = k1 then ()
    else if k0.significant_digits = k1.significant_digits
    then (
      assert (truncate_key_spec k0 k1.significant_digits == k0);
      if is_desc_raw k0 k1
      then is_desc_significant_digits k0 k1
    )
    else is_desc_truncate_key_spec (parent k0) k1

let truncate_is_desc (k0 k1:raw_key)
  : Lemma
    (requires
      good_raw_key k0 /\
      U16.v k0.significant_digits >= U16.v k1.significant_digits)
    (ensures is_desc_raw k0 k1 ==  (truncate_key k0 k1.significant_digits = k1))
  = truncate_key_correct k0 k1.significant_digits;
    is_desc_truncate_key_spec k0 k1

let is_proper_descendent_raw_correct (k0 k1:raw_key)
  : Lemma
    (requires good_raw_key k0)
    (ensures
      is_proper_descendent' k0 k1 == (k0 <> k1 && is_desc_raw k0 k1))
  = if U16.v k0.significant_digits <= U16.v k1.significant_digits
    then (
      assert (not (is_proper_descendent' k0 k1));
      if is_desc_raw k0 k1
      then is_desc_significant_digits k0 k1
    )
    else (
      truncate_is_desc k0 k1
    )

#push-options "--fuel 1 --ifuel 1"
let rec lowered_keys_are_good (ik:Zeta.Key.base_key)
  : Lemma
    (ensures good_raw_key (lower_base_key' ik))
    (decreases ik)
  = let sk = lower_base_key' ik in
    match ik with
    | Zeta.BinTree.Root -> ith_bit_zero ()
    | Zeta.BinTree.LeftChild ik' ->
      lowered_keys_are_good ik';
      let sk' = lower_base_key' ik' in
      assert (forall i. ith_bit sk i == ith_bit sk' i)
    | Zeta.BinTree.RightChild ik' ->
      lowered_keys_are_good ik';
      let sk' = lower_base_key' ik' in
      introduce forall (i:U16.t).
                   U16.v i < 256 /\
                   U16.v sk.significant_digits <= U16.v i ==>
                   ith_bit sk i == ith_bit sk' i
      with (
        FStar.Classical.forall_intro (set_ith_bit_modifies sk' sk'.significant_digits)
      )

let related_proper_descendent_raw (sk0 sk1: raw_key)
                                  (ik0 ik1: Zeta.Key.base_key)
  : Lemma
    (requires
      sk0 == lower_base_key_raw ik0 /\
      sk1 == lower_base_key_raw ik1)
    (ensures
      is_proper_descendent' sk0 sk1 = Zeta.BinTree.is_proper_desc ik0 ik1)
  = lowered_keys_are_good ik0;
    is_proper_descendent_raw_correct sk0 sk1;
    Zeta.BinTree.is_desc_eq ik0 ik1;
    is_desc_raw_related sk0 sk1 ik0 ik1

let truncate_key_extension (k:raw_key)
                           (w:U16.t { U16.(w <^ k.significant_digits) })
  : Lemma
    (requires good_raw_key k)
    (ensures (
      let k0 = truncate_key_spec k w in
      let k' = truncate_key_spec k U16.(w +^ 1us) in
      k'.significant_digits = U16.(w +^ 1us) /\
      (if ith_bit k w
       then k'.k == (set_ith_bit k0 w).k
       else k'.k = k0.k)))
  = let k0 = truncate_key_spec k w in
    let k' = truncate_key_spec k U16.(w +^ 1us) in
    truncate_key_spec_ith_bit k w;
    truncate_key_spec_ith_bit k  U16.(w +^ 1us);
    set_get_ith_bit k0 w;
    if ith_bit k w
    then (
      let k'' =
        { set_ith_bit k0 w
          with significant_digits = k'.significant_digits }
      in
      introduce forall (i:U16.t { U16.v i < 256 }).
                   ith_bit k' i == ith_bit k'' i
      with (
        if U16.v i <= U16.v w
        then assert (ith_bit k' i == ith_bit k i)
      );
      ith_bit_extensional k' k''
    )
    else (
      let k'' =
        { k0
          with significant_digits = k'.significant_digits }
      in
      introduce forall (i:U16.t { U16.v i < 256 }).
                   ith_bit k' i == ith_bit k'' i
      with ();
      ith_bit_extensional k' k''
    )

module B = Zeta.BinTree
let related_desc_dir_raw (sk0 sk1: raw_key) (ik0 ik1: Zeta.Key.base_key)
  : Lemma
    (requires
      sk0 == lower_base_key_raw ik0 /\
      sk1 == lower_base_key_raw ik1 /\
      is_proper_descendent' sk0 sk1)
    (ensures (
      related_proper_descendent_raw sk0 sk1 ik0 ik1;
      desc_dir_raw sk0 sk1 == (Zeta.BinTree.Left? (Zeta.BinTree.desc_dir ik0 ik1))))
  = related_proper_descendent_raw sk0 sk1 ik0 ik1;
    lowered_keys_are_good ik0;
    lowered_keys_are_good ik1;
    let c = B.desc_dir ik0 ik1 in
    if desc_dir_raw sk0 sk1
    then (
      assert (not (ith_bit sk0 sk1.significant_digits));
      assert (truncate_key sk0 sk1.significant_digits ==
              lower_base_key_raw ik1);
      assert (ith_bit
               (lower_base_key_raw (B.LeftChild ik1))
               sk1.significant_digits = false);
      calc (==) {
       truncate_key sk0 U16.(sk1.significant_digits +^ 1us);
      (==) { truncate_key_correct sk0 U16.(sk1.significant_digits +^ 1us) }
       truncate_key_spec sk0 U16.(sk1.significant_digits +^ 1us);
      (==) { truncate_key_extension sk0 sk1.significant_digits }
       ( { truncate_key_spec sk0 U16.(sk1.significant_digits) with
              significant_digits = U16.(sk1.significant_digits +^ 1us) } );
      (==) { truncate_key_correct sk0 U16.(sk1.significant_digits) }
        lower_base_key_raw (B.LeftChild ik1);
      };
      truncate_is_desc
        sk0
        (lower_base_key_raw (B.LeftChild ik1));
      assert (is_desc_raw sk0 (lower_base_key_raw (B.LeftChild ik1)));
      is_desc_raw_related sk0
                      (lower_base_key_raw (B.LeftChild ik1))
                      ik0
                      (B.LeftChild ik1);
      B.is_desc_eq ik0 (B.LeftChild ik1);
      assert (B.is_desc ik0 (B.LeftChild ik1))
    )
    else (
      assert (ith_bit sk0 sk1.significant_digits);
      calc (==) {
       truncate_key sk0 U16.(sk1.significant_digits +^ 1us);
      (==) { truncate_key_correct sk0 U16.(sk1.significant_digits +^ 1us) }
       truncate_key_spec sk0 U16.(sk1.significant_digits +^ 1us);
      (==) { truncate_key_extension sk0 sk1.significant_digits }
       ( { set_ith_bit
              (truncate_key_spec sk0 sk1.significant_digits)
              sk1.significant_digits
           with
              significant_digits = U16.(sk1.significant_digits +^ 1us) } );
      (==) { truncate_key_correct sk0 sk1.significant_digits }
        lower_base_key_raw (B.RightChild ik1);
      };
      truncate_is_desc
        sk0
        (lower_base_key_raw (B.RightChild ik1));
      assert (is_desc_raw sk0 (lower_base_key_raw (B.RightChild ik1)));
      is_desc_raw_related sk0
                      (lower_base_key_raw (B.RightChild ik1))
                      ik0
                      (B.RightChild ik1);
      B.is_desc_eq ik0 (B.RightChild ik1);
      assert (B.is_desc ik0 (B.RightChild ik1))
    )

let rec lift_raw_key_relevant_bits (b0 b1:raw_key)
  : Lemma
    (requires  lift_raw_key b0 == lift_raw_key b1)    
    (ensures   b0.significant_digits = b1.significant_digits /\
              (forall (i:U16.t{U16.v i < U16.v b0.significant_digits}).{:pattern (has_type i U16.t)} ith_bit b0 i == ith_bit b1 i))
    (decreases (U16.v b0.significant_digits))
  = if b0.significant_digits = 0us
    then ()
    else if b0.significant_digits = b1.significant_digits then (
      let b0' = { b0 with significant_digits = U16.(b0.significant_digits -^ 1us) } in
      let b1' = { b1 with significant_digits = U16.(b1.significant_digits -^ 1us) } in
      lift_raw_key_relevant_bits b0' b1'
    )
    else ()

#push-options "--fuel 0 --ifuel 0"
let lower_lift_id (k:raw_key)
  : Lemma 
    (requires good_raw_key k)
    (ensures lower_base_key' (lift_raw_key k) == k)
  = let hk = lift_raw_key k in
    let k' = lower_base_key_raw hk in
    let hk' = lift_raw_key k' in
    lift_lower_id hk;
    assert (hk == hk');
    lowered_keys_are_good hk;
    assert (good_raw_key k');
    lift_raw_key_relevant_bits k k';
    ith_bit_extensional k k'
#pop-options

////////////////////////////////////////////////////////////////////////////////
// Now the main public interface on base_keys
////////////////////////////////////////////////////////////////////////////////
   
let eq_raw_key (k0 k1:raw_key)
  : b:bool { b <==> (k0 == k1) }
  = eq_u256 k0.k k1.k &&
    k0.significant_digits = k1.significant_digits

let eq_base_key (k0 k1:base_key)
  : b:bool { b <==> (k0 == k1) }
  = eq_raw_key k0 k1 
  
let is_internal_key (r:base_key) = U16.(r.significant_digits <^ 256us)

let is_root (r:base_key) = r.significant_digits = 0us

inline_for_extraction
let root_base_key : internal_key =
  FStar.Classical.forall_intro ith_bit_root_raw_key;
  root_raw_key

let is_proper_descendent (k0 k1:base_key) 
  : bool
  = is_proper_descendent' k0 k1

let desc_dir (k0:base_key) (k1:base_key { k0 `is_proper_descendent` k1 })
  : bool
  = desc_dir_raw k0 k1

let lift_base_key (k: base_key)
  : GTot Zeta.Key.base_key
  = lift_raw_key k

let lower_base_key (k:Zeta.Key.base_key)
  : GTot base_key
  = lowered_keys_are_good k;
    lower_base_key_raw k
  
let lift_lower_inv (k:Zeta.Key.base_key)
  : Lemma (lift_base_key (lower_base_key k) == k)
  = lift_lower_id k
  
let lower_lift_inv (k:base_key)
  : Lemma (lower_base_key (lift_base_key k) == k)
  = lower_lift_id k
  
let is_desc (k0 k1:base_key)
  : GTot bool
  = is_desc_raw k0 k1
  
let is_desc_related (k0 k1:base_key)
                    (ik0 ik1:Zeta.Key.base_key)
  : Lemma
    (requires
      k0 == lower_base_key ik0 /\
      k1 == lower_base_key ik1)
    (ensures
      is_desc k0 k1 == Zeta.BinTree.is_desc_aux ik0 ik1)
  = is_desc_raw_related k0 k1 ik0 ik1
  
let is_proper_descendent_correct (k0 k1:base_key)
  : Lemma
    (ensures
      is_proper_descendent k0 k1 <==> (k0 =!= k1 /\ is_desc k0 k1))
  = is_proper_descendent_raw_correct k0 k1
  
let related_proper_descendent (sk0 sk1: base_key)
                              (ik0 ik1: Zeta.Key.base_key)
  : Lemma
    (requires
      sk0 == lower_base_key ik0 /\
      sk1 == lower_base_key ik1)
    (ensures
      is_proper_descendent sk0 sk1 = Zeta.BinTree.is_proper_desc ik0 ik1)
  = related_proper_descendent_raw sk0 sk1 ik0 ik1
  
let related_desc_dir (sk0 sk1: base_key)
                     (ik0 ik1: Zeta.Key.base_key)
  : Lemma
    (requires
      sk0 == lower_base_key ik0 /\
      sk1 == lower_base_key ik1 /\
      is_proper_descendent sk0 sk1)
    (ensures (
      related_proper_descendent sk0 sk1 ik0 ik1;
      desc_dir sk0 sk1 == (Zeta.BinTree.Left? (Zeta.BinTree.desc_dir ik0 ik1))))
  = related_desc_dir_raw sk0 sk1 ik0 ik1

let key_with_descendent_is_internal_key (k':base_key) (k:base_key)
  : Lemma 
    (requires k' `is_proper_descendent` k)
    (ensures is_internal_key k)
  = ()

let lift_internal_key (k:internal_key)
  : Lemma (Zeta.Key.is_merkle_key (lift_base_key k))
  = ()

let lower_merkle_key (k:Zeta.Key.merkle_key)
  : Lemma (is_internal_key (lower_base_key k))
  = ()

let related_root ()
  : Lemma (lift_base_key root_base_key == Zeta.BinTree.Root)
  = ()

let is_root_spec (k:base_key)
  : Lemma (is_root k <==> k==root_base_key)
  = if is_root k 
    then (
      ith_bit_extensional k root_base_key;
      ith_bit_zero ()
    )

let lowered_leaf_key_is_data_key (k:Zeta.Key.leaf_key)
  : Lemma (is_data_key (lower_base_key k))
  = ()

inline_for_extraction
let good_raw_key_impl (r:raw_key)
  : b:bool { b <==> good_raw_key r }
  = let r' = truncate_key r r.significant_digits in
    truncate_key_ith_bit r r.significant_digits;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (ith_bit_extensional r));
    r' = r

