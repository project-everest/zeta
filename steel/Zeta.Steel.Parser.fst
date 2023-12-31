module Zeta.Steel.Parser

(** This module provides the _type_ for a low-level parser for an
 *  given type, i.e., a Steel function that can read a value `v:t`
 *  from a array of bytes.
 **)
open Steel.ST.Util
open Zeta.Steel.Util
module A = Steel.ST.Array
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

let parser_result (b: bytes) (t: Type0) =
  (res: option (t & nat) {
    match res with
    | None -> True
    | Some (_, consumed) -> consumed <= Seq.length b
  })

let spec_parser (t:Type0) =
    b:bytes -> GTot (parser_result b t)

let spec_serializer (#t:Type) (p:spec_parser t) =
    x:t -> GTot (b:bytes{ match p b with
                   | None -> False
                   | Some (y, n) -> x == y /\ n == Seq.length b})

let len_offset_ok (a:byte_array)
                  (len:U32.t)
                  (offset:U32.t) =
  A.length a == U32.v len /\
  U32.v offset < U32.v len


let len_offset_slice_ok (a:byte_array)
                        (len offset slice_len:U32.t) =
  A.length a == U32.v len /\
  U32.v offset + U32.v slice_len <= A.length a

let slice (s:bytes) (from:U32.t) (slice_len:U32.t { slice_ok s from slice_len })
  : bytes
  = Seq.slice s (U32.v from) (U32.v from + U32.v slice_len)

(** A parser for `t` takes a byte array `a` and a proof proof that `a`
    contains `e` at `offset` and tries to parse `Some t` out of the
    contents of `a`
  *)
let parser (#t:Type0) (p:spec_parser t) =
    #perm:perm ->
    len:U32.t ->
    offset:U32.t ->
    slice_len:U32.t ->
    #b:erased bytes { Seq.length b == U32.v len }  ->
    a:byte_array { len_offset_slice_ok a len offset slice_len } ->
    ST (option (t & U32.t))
       (A.pts_to a perm b)
       (fun _ -> A.pts_to a perm b)
       (requires True)
       (ensures fun o ->
         match p (slice b offset slice_len), o with
         | None, None -> True
         | Some (x, n), Some (y, n') -> x == y /\ n == U32.v n'
         | _ -> False)

(** A parser for `t` takes a byte array `a` and a proof proof that `a`
    contains `e` at `offset` and tries to parse `Some t` out of the
    contents of `a`
  *)
let serializer (#t:Type0) (#p:spec_parser t) (s:spec_serializer p) =
    len:U32.t ->
    offset:U32.t ->
    a:byte_array { len_offset_ok a len offset } ->
    v:t { Seq.length (s v) <= U32.v len - U32.v offset } ->
    STT U32.t
        (exists_ (array_pts_to a))
        (fun slice_len ->
            exists_ (fun (bs:_) ->
              array_pts_to a bs `star`
              pure (
                U32.v slice_len == Seq.length (s v) /\
                len_offset_slice_ok a len offset slice_len /\
                Seq.length bs == (U32.v len <: nat) /\
                s v == slice bs offset slice_len )))


let bytes_from (b:bytes)
               (l:U32.t { U32.v l <= Seq.length b })
  : bytes
  = Seq.slice b (U32.v l) (Seq.length b)

let parse_result (log_bytes:bytes)
                 (log_pos:U32.t{
                   U32.v log_pos <= Seq.length log_bytes
                 })
                 (p:spec_parser 'a {
                   Some? (p (bytes_from log_bytes log_pos))
                 })
  : GTot ('a & nat)
  = let Some (le, n) = p (bytes_from log_bytes log_pos) in
    le, n
