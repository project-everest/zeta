module Zeta.Steel.HashValue
open Steel.ST.Util
module T = Zeta.Steel.FormatsManual

val hashfn (v:T.value)
  : GTot T.hash_value

val hasher_t : Type0

val inv : hasher_t -> vprop

val alloc (_:unit)
  : STT hasher_t emp inv

val free (h:hasher_t)
  : STT unit (inv h) (fun _ -> emp)

val hash_value (h:hasher_t)
               (v:T.value)
  : ST T.hash_value
    (inv h)
    (fun _ -> inv h)
    (requires True)
    (ensures fun res -> hashfn v == res)
