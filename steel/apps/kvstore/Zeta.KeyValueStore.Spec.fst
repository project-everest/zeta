module Zeta.KeyValueStore.Spec

open Zeta.App

module P = Zeta.Steel.Parser
module F = Zeta.KeyValueStore.Formats

friend Zeta.Steel.KeyUtils

let key_hash_fn (k:F.key_t) : Zeta.Key.leaf_key =
    let rk : Zeta.Steel.KeyUtils.raw_key = {
    k = ({
      v3 = 0uL;
      v2 = 0uL;
      v1 = 0uL;
      v0 = k;
    });

   significant_digits = 256us;
  } in
  Zeta.Steel.KeyUtils.lift_raw_key rk
let key_cmp_fn = fun n1 n2 -> FStar.UInt64.(n1 <=^ n2)

let value_hash_fn _ = Zeta.Hash.zero
let value_cmp_fn =
  fun v1 v2 ->
  match v1, v2 with
  | Null, _ -> true
  | DValue v1, DValue v2 -> FStar.UInt64.(v1 <=^ v2)
  | _, _ -> false
