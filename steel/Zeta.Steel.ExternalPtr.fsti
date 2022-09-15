module Zeta.Steel.ExternalPtr

// DO NOT FRIEND this module!

module A = Steel.ST.Array
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open Steel.ST.Util

inline_for_extraction
val extern_input_ptr : Type0

val has_extern_input_ptr (e: extern_input_ptr) (n: U32.t) : vprop

inline_for_extraction
val copy_extern_input_ptr
  (e: extern_input_ptr)
  (n: U32.t)
  (a: A.array U8.t)
: ST bool
    (has_extern_input_ptr e n `star` exists_ (fun contents -> A.pts_to a full_perm contents))
    (fun _ -> has_extern_input_ptr e n `star` exists_ (fun contents -> A.pts_to a full_perm contents))
    (A.length a == U32.v n)
    (fun _ -> True)
