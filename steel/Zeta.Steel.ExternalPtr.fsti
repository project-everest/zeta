module Zeta.Steel.ExternalPtr
include Zeta.Steel.ExternalPtr.SLAnd

// DO NOT FRIEND this module!

module A = Steel.ST.Array
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open Steel.ST.Util

inline_for_extraction
val extern_input_ptr : Type0

val has_extern_input_ptr (e: extern_input_ptr) (n: U32.t) : vprop

inline_for_extraction
val valid_input (p: extern_input_ptr) (n: U32.t) : Tot bool

inline_for_extraction
val copy_extern_input_ptr
  (e: extern_input_ptr)
  (n: U32.t)
: ST (A.array U8.t)
    (has_extern_input_ptr e n)
    (fun res -> has_extern_input_ptr e n `star` exists_ (fun contents -> A.pts_to res full_perm contents))
    (valid_input e n)
    (fun res -> A.is_full_array res /\ A.length res == U32.v n)

inline_for_extraction
val extern_output_ptr: Type0

val gtake (p: extern_output_ptr) : GTot (A.array U8.t)

inline_for_extraction
val valid_output (p: extern_output_ptr) (n: U32.t) : Pure bool
  (requires True)
  (ensures (fun b -> b == true ==> U32.v n == A.length (gtake p)))

inline_for_extraction
val take (p: extern_output_ptr) (n: Ghost.erased U32.t) : Pure (A.array U8.t)
  (requires (valid_output p n))
  (ensures (fun y -> y == gtake p))

let check_disjoint_post
  (b: bool)
  (p1 p2: vprop)
: vprop
= p1 `(if b then star else sl_and)` p2

inline_for_extraction
val check_input_output_disjoint
  (input: extern_input_ptr)
  (input_len: U32.t)
  (output: extern_output_ptr)
  (output_len: U32.t)
  (output_contents: Ghost.erased (Seq.seq U8.t))
: ST bool
    (has_extern_input_ptr input input_len `sl_and` A.pts_to (gtake output) full_perm output_contents)
    (fun b -> check_disjoint_post b (has_extern_input_ptr input input_len) (A.pts_to (gtake output) full_perm output_contents))
    (valid_input input input_len /\ valid_output output output_len)
    (fun _ -> True)
