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

let related_zero_u64 ()
  : Lemma (UInt.to_vec (U64.v 0uL) `Seq.equal`
           FStar.BitVector.zero_vec #64)
  = assert (U64.v 0uL == UInt.zero 64)

let zero: T.hash_value =
  let open T in
  let z = U64.zero in
  { v3 = z; v2 = z; v1 = z ; v0 = z }

let related_zero ()
  : Lemma (bitvec_of_u256 zero ==
           FStar.BitVector.zero_vec #256)
  = related_zero_u64();
    assert (bitvec_of_u256 zero `Seq.equal`
           FStar.BitVector.zero_vec #256)  
  
let u64_of_bitvec (x:FStar.BitVector.bv_t 64) 
  : GTot U64.t
  = U64.uint_to_t (UInt.from_vec x)

let u256_of_bitvec (x:FStar.BitVector.bv_t 256) 
  : GTot T.u256
  = { v0 = u64_of_bitvec (Seq.slice x 0 64);
      v1 = u64_of_bitvec (Seq.slice x 64 128);
      v2 = u64_of_bitvec (Seq.slice x 128 192);
      v3 = u64_of_bitvec (Seq.slice x 192 256)}

#push-options "--fuel 0 --ifuel 0"
let inverse (x:FStar.BitVector.bv_t 256)
  : Lemma (bitvec_of_u256 (u256_of_bitvec x) `Seq.equal` x)
  = let t = u256_of_bitvec x in
    assert (UInt.to_vec (U64.v t.v0) `Seq.equal` (Seq.slice x 0 64));
    assert (UInt.to_vec (U64.v t.v1) `Seq.equal` (Seq.slice x 64 128));
    assert (UInt.to_vec (U64.v t.v2) `Seq.equal` (Seq.slice x 128 192));
    assert (UInt.to_vec (U64.v t.v3) `Seq.equal` (Seq.slice x 192 256))
#pop-options

