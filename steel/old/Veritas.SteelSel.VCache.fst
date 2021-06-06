module Veritas.SteelSel.VCache

let is_value_of (k:key) (v:value) = admit()
let is_data_key (k:key) : bool = admit()

let vcache_create n = alloc None n

let vcache_get_record vst s = index vst s

let vcache_set st s r = upd st s r
