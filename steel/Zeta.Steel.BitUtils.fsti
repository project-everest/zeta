module Zeta.Steel.BitUtils

module T = Zeta.Steel.FormatsManual

let bv_t = FStar.BitVector.bv_t

val bitvec_of_u256 (i: T.u256)
  : bv_t 256

val bitvec_of_u256_inj (i j:_)
  : Lemma
    (ensures bitvec_of_u256 i == bitvec_of_u256 j ==>
             i == j)
    [SMTPat (bitvec_of_u256 i);
     SMTPat (bitvec_of_u256 j)]
