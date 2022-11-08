module Zeta.Steel.ExternalPtr

// DO NOT FRIEND this module!

module A = Steel.ST.Array
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open Steel.ST.Util

inline_for_extraction
val extern_ptr : Type0

[@@erasable]
noeq
type state =
| Unread: (out_len: SizeT.t) -> state
| Read: (out_len: SizeT.t) -> state
| Written: (written: Seq.seq U8.t) -> state

val extern_in_out_pts_to (e1: extern_ptr) (e2: extern_ptr) (in_contents: Seq.seq U8.t) (s: state) : vprop

[@@__reduce__]
let is_valid_state_true
  (e1: extern_ptr)
  (n1: SizeT.t)
  (e2: extern_ptr)
  (n2: SizeT.t)
: Tot vprop
= exists_ (fun in_contents ->
    extern_in_out_pts_to e1 e2 in_contents (Unread n2) `star`
    pure (SizeT.v n1 == Seq.length in_contents)
  )

let is_valid_state
  (e1: extern_ptr)
  (n1: SizeT.t)
  (e2: extern_ptr)
  (n2: SizeT.t)
  (b: bool)
: Tot vprop
= if b then is_valid_state_true e1 n1 e2 n2 else emp

val extern_in_out_pts_to_is_valid
  (e1: extern_ptr)
  (n1: SizeT.t)
  (e2: extern_ptr)
  (n2: SizeT.t)
: STT bool
  emp
  (fun b -> is_valid_state e1 n1 e2 n2 b)

inline_for_extraction
val copy_extern_input_ptr
  (e1: extern_ptr)
  (w1: Ghost.erased (Seq.seq U8.t))
  (e2: extern_ptr)
  (n: SizeT.t)
  (out_len: Ghost.erased SizeT.t)
  (a: A.array U8.t)
: ST unit
    (extern_in_out_pts_to e1 e2 w1 (Unread out_len) `star` exists_ (fun contents -> A.pts_to a full_perm contents))
    (fun _ ->
      extern_in_out_pts_to e1 e2 w1 (Read out_len) `star` A.pts_to a full_perm w1
    )
    (A.length a == SizeT.v n /\
      Seq.length w1 == SizeT.v n)
    (fun _ -> True)

inline_for_extraction
val copy_extern_output_ptr
  (e1: extern_ptr)
  (w1: Ghost.erased (Seq.seq U8.t))
  (e2: extern_ptr)
  (n: SizeT.t)
  (a: A.array U8.t)
  (p: perm)
  (contents: Ghost.erased (Seq.seq U8.t))
: ST unit
    (extern_in_out_pts_to e1 e2 w1 (Read n) `star` A.pts_to a p contents)
    (fun _ ->
      extern_in_out_pts_to e1 e2 w1 (Written contents) `star` A.pts_to a p contents
    )
    (A.length a == SizeT.v n)
    (fun _ -> True)
