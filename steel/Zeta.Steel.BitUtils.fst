module Zeta.Steel.BitUtils

module T = Zeta.Steel.FormatsManual
module L = FStar.List.Tot
module U64 = FStar.UInt64
module BV = FStar.BV


let bitvec_of_u256 (i:T.u256) : FStar.BitVector.bv_t 256 =
  (UInt.to_vec (U64.v i.v0)) `Seq.append` (
  (UInt.to_vec (U64.v i.v1)) `Seq.append` (
  (UInt.to_vec (U64.v i.v2)) `Seq.append` (
  (UInt.to_vec (U64.v i.v3)))))

let bitvec_of_u64_inj  (i j:U64.t)
  : Lemma
    (ensures
      UInt.to_vec (U64.v i) == UInt.to_vec (U64.v j) ==>
      i == j)
  = UInt.inverse_num_lemma (U64.v i);
    UInt.inverse_num_lemma (U64.v j)

let bitvec_of_u256_inj (i j:_)
  : Lemma
    (ensures bitvec_of_u256 i == bitvec_of_u256 j ==>
             i == j)
  = bitvec_of_u64_inj i.v0 j.v0;
    bitvec_of_u64_inj i.v1 j.v1;
    bitvec_of_u64_inj i.v2 j.v2;
    bitvec_of_u64_inj i.v3 j.v3;
    if bitvec_of_u256 i = bitvec_of_u256 j
    then (
    Seq.lemma_append_inj
      (UInt.to_vec (U64.v i.v0))
      ((UInt.to_vec (U64.v i.v1)) `Seq.append` (
       (UInt.to_vec (U64.v i.v2)) `Seq.append` (
       (UInt.to_vec (U64.v i.v3)))))
      (UInt.to_vec (U64.v j.v0))
      ((UInt.to_vec (U64.v j.v1)) `Seq.append` (
       (UInt.to_vec (U64.v j.v2)) `Seq.append` (
       (UInt.to_vec (U64.v j.v3)))));
    Seq.lemma_append_inj
      (UInt.to_vec (U64.v i.v1))
      ((UInt.to_vec (U64.v i.v2)) `Seq.append` (
       (UInt.to_vec (U64.v i.v3))))
      (UInt.to_vec (U64.v j.v1))
       ((UInt.to_vec (U64.v j.v2)) `Seq.append` (
       (UInt.to_vec (U64.v j.v3))));
    Seq.lemma_append_inj
      (UInt.to_vec (U64.v i.v2))
      (UInt.to_vec (U64.v i.v3))
      (UInt.to_vec (U64.v j.v2))
      (UInt.to_vec (U64.v j.v3))
    )
