module Zeta.Steel.RelHashFunction
open Zeta.Steel.Rel

(* the hash of two related values is related *)
val related_hashfn (sv: s_val) (iv: i_val)
  : Lemma (requires (related_val sv iv))
          (ensures (related_hash_value (s_hashfn sv) (i_hashfn iv)))
