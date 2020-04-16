module Veritas.Blum

open FStar.BitVector

(* Size of a hash value *)
let hash_size = 128

(* hash value - bit vector of a specified size *)
type hash_value = bv_t 

(* epoch is a nat number *)
type epoch = nat

