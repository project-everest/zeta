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

val extract_log_entry_from (len: U32.t) (buf: A.array U8.t { A.length buf == U32.v len }) (pos: ref (x: U32.t { U32.v x <= U32.v len }))
  : Steel (option vlog_entry)
    (A.varray buf `star` vptr pos)
    (fun _ -> A.varray buf `star` vptr pos)
    (fun _ -> True)
    (fun h res h' ->
      let p = h (vptr pos) in
      let p' = h' (vptr pos) in
      U32.v p <= U32.v p' /\
      h' (A.varray buf) == h (A.varray buf) /\
      begin match res with
      | None -> True
      | Some v ->
        parsed (Seq.slice (h (A.varray buf)) (U32.v p) (U32.v p')) v
      end
    )

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
    Seq.slice s' (U32.v len) (Seq.length s') == Seq.slice s (U32.v len) (Seq.length s)
  )
