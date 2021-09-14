module Veritas.Formats
include Veritas.Formats.Pure

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module A = Steel.Array

open Steel.Effect.Common
open Steel.Effect
open Steel.Reference

val serialize_value: v:value -> dst: A.array U8.t { A.length dst == U32.v (serialize_length v) } ->
  SteelT unit
    (A.varray dst)
    (fun _ -> A.varray dst)

module R = Steel.Reference

inline_for_extraction
noextract
let bounded_u32 (l:nat) = x:U32.t { U32.v x <= l }

let larray t (l:U32.t) = a:A.array t { A.length a == U32.v l }

let valid_entry' (s:Seq.seq U8.t) (from:nat) (to:nat) (e:vlog_entry)
  : prop
  = from < to /\
    to <= Seq.length s /\
    parsed (Seq.slice s from to) e

[@@"opaque_to_smt"]
let valid_entry = valid_entry'

let valid_entry_pos_lt (s:Seq.seq U8.t) (pos pos':nat) (e:vlog_entry)
  : Lemma
    (requires
      valid_entry s pos pos' e)
    (ensures
      pos < pos')
  = reveal_opaque (`%valid_entry) valid_entry

let valid_entry_slice (s s':_) (from to from' to':_) (e:_)
  : Lemma
    (requires
      from < to /\
      to <= Seq.length s /\
      from' < to' /\
      to' <= Seq.length s' /\
      Seq.equal (Seq.slice s from to)
                (Seq.slice s' from' to') /\
      valid_entry s from to e)
    (ensures
      valid_entry s' from' to' e)
  = reveal_opaque (`%valid_entry) valid_entry

val extract_log_entry_from (len: U32.t)
                           (buf: larray U8.t len)
                           (pos: bounded_u32 (U32.v len))
  : Steel (either (vlog_entry & bounded_u32 (U32.v len))
                  (bounded_u32 (U32.v len) & string))
    (A.varray buf)
    (fun _ -> A.varray buf)
    (requires fun _ -> True)
    (ensures fun h0 x h1 ->
      A.asel buf h0 == A.asel buf h1 /\
      (match x with
       | Inl (e, pos') ->
         valid_entry (A.asel buf h0) (U32.v pos) (U32.v pos') e
       | _ -> True))

val serialize_stamped_record_spec (r:stamped_record)
  : GTot (s:Seq.seq U8.t { Seq.length s <= 184 })

val serialize_stamped_record
  (dst: A.array U8.t { 184 <= A.length dst })
  (r: stamped_record)
: Steel U32.t
  (A.varray dst)
  (fun _ -> A.varray dst)
  (fun _ -> True)
  (fun h len h' ->
    let s = h (A.varray dst) in
    let s' = h' (A.varray dst) in
    U32.v len <= A.length dst /\
    Seq.slice s' (U32.v len) (Seq.length s') == Seq.slice s (U32.v len) (Seq.length s) /\
    (* Possible to add this? *)
    Seq.slice s' 0 (U32.v len) == serialize_stamped_record_spec r
  )
