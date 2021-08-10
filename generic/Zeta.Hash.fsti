module Zeta.Hash

open FStar.BitVector

(* size of a hash value *)
let hash_size = 256

(* hash value *)
type hash_value = bv_t hash_size
