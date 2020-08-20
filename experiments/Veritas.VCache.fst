module Veritas.VCache

open FStar.HyperStack
open FStar.HyperStack.ST

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

module B = LowStar.Buffer

module C = FStar.Int.Cast

type data_t = magic ()

let most_significant_bit k = magic ()

type vstore = B.lbuffer (option record) (UInt.max_int U16.n)

let invariant st h =
  B.live h st

let footprint st = B.loc_buffer st

let as_seq st h = B.as_seq h st

let frame_invariant _ _ _ _ = ()

let vcache_create () =
  B.gcmalloc #(option record) HS.root None (U32.uint_to_t (UInt.max_int U16.n))

let vcache_get_record st s = B.index st (C.uint16_to_uint32 s)

let vcache_update_record st s r = B.upd st (C.uint16_to_uint32 s) (Some r)

let vcache_add_record st s k v _a = vcache_update_record st s (k, v)

let vcache_evict_record st s _k = B.upd st (C.uint16_to_uint32 s) None
