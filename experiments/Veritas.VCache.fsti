module Veritas.VCache

open FStar.HyperStack
open FStar.HyperStack.ST

include Veritas.Formats

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

(* size of a hash value *)
let hash_size : nat = 256

val most_significant_bit (k:key) : bool

let is_data_key (k:key) : bool = most_significant_bit k

let is_value_of (k:key) (v:value)
  : bool
  = if is_data_key k then V_dval? v else V_mval? v

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

// JP: so that, given a vstore in scope whose invariant holds, client can deduce
// disjointness of their own fresh allocations from the vstore footprint
val invariant_loc_in_footprint: h:HS.mem -> st:vstore -> Lemma
    (requires (invariant st h))
    (ensures (B.loc_in (footprint st) h))
    [ SMTPat (invariant st h) ]


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
        r == Seq.index (as_seq st h1) (U16.v (get_slot_id s)))

val vcache_update_record (st:vstore) (s:slot_id) (r:record)
  : Stack unit
      (requires fun h -> invariant st h)
      (ensures fun h0 _ h1 ->
        B.(modifies (footprint st) h0 h1) /\
        invariant st h1 /\
        as_seq st h1 == Seq.upd (as_seq st h0) (U16.v (get_slot_id s)) (Some r))

let mk_record k v a : record = {
  record_key = k;
  record_value = v;
  record_add_method = a;
  record_l_child_in_store = Vfalse;
  record_r_child_in_store = Vfalse;
}

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
        as_seq st h1 == Seq.upd (as_seq st h0) (U16.v (get_slot_id s)) (Some (mk_record k v a)))

val vcache_evict_record (st:vstore) (s:slot_id) (k:key)  //AR: Do we need k here?
  : Stack unit
      (requires fun h -> invariant st h)
      (ensures fun h0 _ h1 ->
        B.(modifies (footprint st) h0 h1) /\
        invariant st h1 /\
        as_seq st h1 == Seq.upd (as_seq st h0) (U16.v (get_slot_id s)) None)
