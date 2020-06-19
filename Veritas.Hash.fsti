module Veritas.Hash

open FStar.BitVector
open Veritas.Record

(* size of a hash value *)
let hash_size = 256

(* hash value *)
type hash_value = bv_t hash_size

(* hash function maps a merkle payload to a hash value *)
val hashfn (v:value): Tot hash_value
