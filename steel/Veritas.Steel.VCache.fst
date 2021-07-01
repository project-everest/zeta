module Veritas.Steel.VCache

let vcache_create n = malloc None n

assume
val uint16_to_uint32 (n:U16.t) : Tot (v:U32.t{U32.v v == U16.v n})

let vcache_get_record vst s = index vst (uint16_to_uint32 s)

let vcache_set st s r = upd st (uint16_to_uint32 s) r
