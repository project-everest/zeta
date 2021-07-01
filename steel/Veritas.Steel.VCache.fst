module Veritas.Steel.VCache

let vcache_create n = malloc None n

let vcache_get_record vst s = index vst s

let vcache_set st s r = upd st s r
