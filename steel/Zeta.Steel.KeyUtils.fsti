module Zeta.Steel.KeyUtils
module U64 = FStar.UInt64

type u256 = {
  v3 : U64.t;
  v2 : U64.t;
  v1 : U64.t;
  v0 : U64.t;
}


let eq_u256 (i0 i1: u256)
  : Tot (b:bool { b <==>  (i0 == i1) })
  = i0.v0 = i1.v0 &&
    i0.v1 = i1.v1 &&
    i0.v2 = i1.v2 &&
    i0.v3 = i1.v3
  
val base_key
  : Type0

val eq_base_key (k0 k1:base_key)
  : b:bool { b <==> (k0 == k1) }

val is_internal_key (b:base_key)
  : bool

let is_data_key (k:base_key)
  : bool
  = not (is_internal_key k)
  
val is_root (k:base_key)
  : bool

let internal_key
  : Type0
  = k:base_key { is_internal_key k }

val root_base_key
  : internal_key

val is_proper_descendent (k0 k1:base_key)
  : bool

val desc_dir (k0:base_key) (k1:base_key { k0 `is_proper_descendent` k1 })
  : bool

val lift_base_key (k: base_key)
  : GTot Zeta.Key.base_key

val lower_base_key (k:Zeta.Key.base_key)
  : GTot base_key

val lift_lower_inv (k:Zeta.Key.base_key)
  : Lemma (lift_base_key (lower_base_key k) == k)

val lower_lift_inv (k:base_key)
  : Lemma (lower_base_key (lift_base_key k) == k)

val is_desc (k0 k1:base_key)
  : GTot bool
  
val is_desc_related (k0 k1:base_key)
                    (ik0 ik1:Zeta.Key.base_key)
  : Lemma
    (requires
      k0 == lower_base_key ik0 /\
      k1 == lower_base_key ik1)
    (ensures
      is_desc k0 k1 == Zeta.BinTree.is_desc_aux ik0 ik1)

val is_proper_descendent_correct (k0 k1:base_key)
  : Lemma
    (ensures
      is_proper_descendent k0 k1 <==> (k0 =!= k1 /\ is_desc k0 k1))

val related_proper_descendent (sk0 sk1: base_key)
                              (ik0 ik1: Zeta.Key.base_key)
  : Lemma
    (requires
      sk0 == lower_base_key ik0 /\
      sk1 == lower_base_key ik1)
    (ensures
      is_proper_descendent sk0 sk1 = Zeta.BinTree.is_proper_desc ik0 ik1)

val related_desc_dir (sk0 sk1: base_key)
                     (ik0 ik1: Zeta.Key.base_key)
  : Lemma
    (requires
      sk0 == lower_base_key ik0 /\
      sk1 == lower_base_key ik1 /\
      is_proper_descendent sk0 sk1)
    (ensures (
      related_proper_descendent sk0 sk1 ik0 ik1;
      desc_dir sk0 sk1 == (Zeta.BinTree.Left? (Zeta.BinTree.desc_dir ik0 ik1))))

val key_with_descendent_is_internal_key (k':base_key) (k:base_key)
  : Lemma 
    (requires k' `is_proper_descendent` k)
    (ensures is_internal_key k)

val lift_internal_key (k:internal_key)
  : Lemma (Zeta.Key.is_merkle_key (lift_base_key k))

val lower_merkle_key (k:Zeta.Key.merkle_key)
  : Lemma (is_internal_key (lower_base_key k))

val related_root (_:unit)
  : Lemma (lift_base_key root_base_key == Zeta.BinTree.Root)

val is_root_spec (k:base_key)
  : Lemma (is_root k <==> k==root_base_key)

val lowered_leaf_key_is_data_key (k:Zeta.Key.leaf_key)
  : Lemma (is_data_key (lower_base_key k))

