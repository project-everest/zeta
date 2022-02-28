module Zeta.Steel.BitUtils

module T = Zeta.Steel.FormatsManual
module L = FStar.List.Tot
module U64 = FStar.UInt64
module BV = FStar.BV

[@@"opaque_to_smt"]
let bv_of_u256 (i:T.u256) : BV.bv_t 256 =
  let open T in
  let open L in
  let bv0 = BV.bv2list (BV.int2bv #64 (U64.v (i.v0))) in
  let bv1 = BV.bv2list (BV.int2bv #64 (U64.v (i.v1))) in
  let bv2 = BV.bv2list (BV.int2bv #64 (U64.v (i.v2))) in
  let bv3 = BV.bv2list (BV.int2bv #64 (U64.v (i.v3))) in
  BV.list2bv (bv0@bv1@bv2@bv3)

[@@"opaque_to_smt"]
let bitvec_of_u256 (i:T.u256) : FStar.BitVector.bv_t 256 =
  Seq.seq_of_list (BV.bv2list (bv_of_u256 i))

let bitvec_of_u256_inj (i j:_)
  : Lemma
    (ensures bitvec_of_u256 i == bitvec_of_u256 j ==>
             i == j)
  = admit()
