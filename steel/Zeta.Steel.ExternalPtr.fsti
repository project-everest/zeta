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
| Unknown: (in_contents: Seq.seq U8.t) -> state
| Unread: (in_contents: Seq.seq U8.t) -> (out_len: U32.t) -> state
| Read: (in_contents: Seq.seq U8.t) -> (out_len: U32.t) -> state
| Written: (in_len: nat) -> (written: Seq.seq U8.t) -> state

let get_in_contents
  (s: state)
: Ghost (Seq.seq U8.t)
    (requires (~ (Written? s)))
    (ensures (fun _ -> True))
= match s with
  | Unknown in_contents
  | Unread in_contents _
  | Read in_contents _
    -> in_contents

val extern_in_out_pts_to (e1: extern_ptr) (e2: extern_ptr) (s: state) : vprop

let is_valid_state (b: bool) (in_contents: Seq.seq U8.t) (out_len: U32.t) : Tot state =
  if b then Unread in_contents out_len else Unknown in_contents

val extern_in_out_pts_to_is_valid
  (e1: extern_ptr)
  (w1: Ghost.erased (Seq.seq U8.t))
  (n1: U32.t)
  (e2: extern_ptr)
  (n2: U32.t)
: ST bool
  (extern_in_out_pts_to e1 e2 (Unknown w1))
  (fun b -> extern_in_out_pts_to e1 e2 (is_valid_state b w1 n2))
  True
  (fun b -> b == true ==> (
    U32.v n1 == Seq.length w1
  ))

inline_for_extraction
val copy_extern_input_ptr
  (e1: extern_ptr)
  (w1: Ghost.erased (Seq.seq U8.t))
  (e2: extern_ptr)
  (n: U32.t)
  (out_len: Ghost.erased U32.t)
  (a: A.array U8.t)
: ST unit
    (extern_in_out_pts_to e1 e2 (Unread w1 out_len) `star` exists_ (fun contents -> A.pts_to a full_perm contents))
    (fun _ ->
      extern_in_out_pts_to e1 e2 (Read w1 out_len) `star` A.pts_to a full_perm w1
    )
    (A.length a == U32.v n /\
      Seq.length w1 == U32.v n)
    (fun _ -> True)

inline_for_extraction
val copy_extern_output_ptr
  (e1: extern_ptr)
  (w1: Ghost.erased (Seq.seq U8.t))
  (e2: extern_ptr)
  (in_len: Ghost.erased nat)
  (n: U32.t)
  (a: A.array U8.t)
  (p: perm)
  (contents: Ghost.erased (Seq.seq U8.t))
: ST unit
    (extern_in_out_pts_to e1 e2 (Read w1 n) `star` A.pts_to a p contents)
    (fun _ ->
      extern_in_out_pts_to e1 e2 (Written in_len contents) `star` A.pts_to a p contents
    )
    (A.length a == U32.v n /\
      Seq.length w1 == Ghost.reveal in_len)
    (fun _ -> True)
