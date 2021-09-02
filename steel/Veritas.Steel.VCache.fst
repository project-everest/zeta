module Veritas.Steel.VCache
module C = FStar.Int.Cast

let vcache_create n =
  let h = get () in //TODO: need this unnecessarily
  malloc None (C.uint16_to_uint32 n)

let free #n v = Steel.Array.free v

let vcache_get_record vst s =
  index vst (C.uint16_to_uint32 s)

let vcache_set st s r = upd st (C.uint16_to_uint32 s) r
