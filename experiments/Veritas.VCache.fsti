module Veritas.VCache

open FStar.HyperStack
open FStar.HyperStack.ST

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128

module HS = FStar.HyperStack

module B = LowStar.Buffer

type u8  = U8.t
type u16 = U16.t
type u32 = U32.t
type u64 = U64.t
type u128 = U128.t

type slot_id = n:u16{U16.v n < UInt.max_int U16.n}

type u256 = u64 & u64 & u64 & u64

type key = u256 & u8  //size of a merkle key, excluding leading zeroes

val data_t : eqtype //Pick a concrete data value?

let data_value = option data_t

(* size of a hash value *)
let hash_size : nat = 256

(* hash value *)
type hash_value = u128 & u128

(* information about a desc stored in a merkle node *)
type descendent_hash =
  | Empty: descendent_hash
  | Desc: k:key -> //Q: do we really need to store this here? I guess because its sparse we can't compute the key of the descendent?
          h:hash_value ->
          evicted_to_blum:bool -> //Q: What does this represent?
          in_store:bool -> //The descendent with key k is in the VStore
          descendent_hash

type value =
  | MVal : l:descendent_hash -> r:descendent_hash -> value
  | DVal : data_value -> value

type record = key & value

type add_method =
  | MAdd: add_method  (* AddM *)
  | BAdd: add_method  (* AddB *)

val most_significant_bit (k:key) : bool

let is_data_key (k:key) : bool = most_significant_bit k

let is_value_of (k:key) (v:value)
  : bool
  = if is_data_key k then DVal? v else MVal? v

val vstore : Type0

val invariant (st:vstore) (h:HS.mem) : Type0

val footprint (st:vstore) : GTot B.loc

val as_seq (st:vstore) (h:HS.mem)
  : GTot (Seq.lseq (option record) (UInt.max_int U16.n))

val frame_invariant (st:vstore) (l:B.loc) (h0 h1:HS.mem)
  : Lemma
      (requires
        invariant st h0 /\
        B.modifies l h0 h1 /\
        B.loc_disjoint l (footprint st))
      (ensures invariant st h1)
      [SMTPat (invariant st h1); SMTPat (B.modifies l h0 h1)]

val vcache_create (_:unit)
  : ST vstore
      (requires fun h -> True)
      (ensures fun h0 st h1 ->
        B.(modifies loc_none h0 h1) /\
        invariant st h1 /\
        B.fresh_loc (footprint st) h0 h1 /\
        as_seq st h1 == Seq.create (UInt.max_int U16.n) None)

val vcache_get_record (st:vstore) (s:slot_id)
  : Stack (option record)
      (requires fun h -> invariant st h)
      (ensures fun h0 r h1 ->
        h0 == h1 /\
        r == Seq.index (as_seq st h1) (U16.v s))

val vcache_update_record (st:vstore) (s:slot_id) (r:record)
  : Stack unit
      (requires fun h -> invariant st h)
      (ensures fun h0 _ h1 ->
        B.(modifies (footprint st) h0 h1) /\
        invariant st h1 /\
        as_seq st h1 == Seq.upd (as_seq st h0) (U16.v s) (Some r))

val vcache_add_record  //AR: Difference from vcache_update_record?
  (st:vstore)
  (s:slot_id)
  (k:key)
  (v:value{is_value_of k v})
  (a:add_method)
  : Stack unit
      (requires fun h -> invariant st h)
      (ensures fun h0 _ h1 ->
        B.(modifies (footprint st) h0 h1) /\
        invariant st h1 /\
        as_seq st h1 == Seq.upd (as_seq st h0) (U16.v s) (Some (k, v)))

val vcache_evict_record (st:vstore) (s:slot_id) (k:key)  //AR: Do we need k here?
  : Stack unit
      (requires fun h -> invariant st h)
      (ensures fun h0 _ h1 ->
        B.(modifies (footprint st) h0 h1) /\
        invariant st h1 /\
        as_seq st h1 == Seq.upd (as_seq st h0) (U16.v s) None)
