module Zeta.Steel.Parser

(** This module provides the _type_ for a low-level parser for an
 *  given type, i.e., a Steel function that can read a value `v:t`
 *  from a array of bytes.
 **)
open Steel.FractionalPermission
open Steel.Effect
open Steel.Effect.Atomic
module A = Steel.Array
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
open FStar.Ghost

let byte = U8.t

let byte_array = A.array byte
let bytes = Seq.seq byte

(** The slice of `s` starting at `offset`
    and continuing for `length e` bytes is defined
  *)
let slice_ok (s:bytes) (from slice_len:U32.t) =
  let to = U32.v from + U32.v slice_len in
  Seq.length s >= to

(** An abstract predicate stating that `b` can be parsed as `x`
  *   -- We will need some lemmas about this, injectivity etc.
  *      so that it can be composed with LowParse
  *)
let spec_parser (t:Type0) =
    b:bytes -> option (t & n:nat{n <= Seq.length b})

let spec_serializer (#t:Type) (p:spec_parser t) =
    x:t -> b:bytes{ match p b with
                   | None -> False
                   | Some (y, n) -> x == y /\ n == Seq.length b}

let len_offset_ok (a:Parser.byte_array)
                  (len:U32.t)
                  (offset:U32.t) =
  A.length a == U32.v len /\
  U32.v offset < U32.v len


let len_offset_slice_ok (a:Parser.byte_array)
                        (len offset slice_len:U32.t) =
  len_offset_ok a len offset /\
  U32.v offset + U32.v slice_len <= A.length a

let slice (s:bytes) (from:U32.t) (slice_len:U32.t { slice_ok s from slice_len })
  : bytes
  = Seq.slice s (U32.v from) (U32.v from + U32.v slice_len)

(** A parser for `t` takes a byte array `a` and a proof proof that `a`
    contains `e` at `offset` and tries to parse `Some t` out of the
    contents of `a`
  *)
let parser (#t:Type0) (p:spec_parser t) =
    len:U32.t ->
    offset:U32.t ->
    slice_len:U32.t ->
    a:byte_array { len_offset_slice_ok a len offset slice_len } ->
    Steel (option t)
          (A.varray a)
          (fun _ -> A.varray a)
          (requires fun h -> True)
          (ensures fun h0 o h1 ->
            A.asel a h0 == A.asel a h1 /\
            (match p (slice (A.asel a h0) offset slice_len), o with
             | None, None -> True
             | Some (x, n), Some y -> x == y /\ n == U32.v slice_len
             | _ -> False))

(** A parser for `t` takes a byte array `a` and a proof proof that `a`
    contains `e` at `offset` and tries to parse `Some t` out of the
    contents of `a`
  *)
let serializer (#t:Type0) (#p:spec_parser t) (s:spec_serializer p) =
    len:U32.t ->
    offset:U32.t ->
    a:byte_array { len_offset_ok a len offset } ->
    v:t ->
    Steel (option U32.t)
          (A.varray a)
          (fun _ -> A.varray a)
          (requires fun h -> True)
          (ensures fun h0 o h1 ->
            let initial = A.asel a h0 in
            let final = A.asel a h1 in
            slice initial 0ul offset == slice final 0ul offset /\
            (match o with
             | None -> True // serialization failed
             | Some slice_len ->
               len_offset_slice_ok a len offset slice_len /\
               s v == slice final offset slice_len))
