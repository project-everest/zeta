module Veritas.Formats
include Veritas.Formats.Pure

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module A = Steel.Array

open Steel.Effect.Common
open Steel.Effect

val serialize_value: v:value -> dst: A.array U8.t { A.length dst == U32.v (serialize_length v) } ->
  SteelT unit
    (A.varray dst)
    (fun _ -> A.varray dst)

val extract_log_entry_from (len: U32.t) (buf: A.array U8.t { A.length buf == U32.v len }) (pos: A.array (x: U32.t { U32.v x <= U32.v len }) { A.length pos == 1 })
  : SteelT (option vlog_entry)
    (A.varray buf `star` A.varray pos)
    (fun _ -> A.varray buf `star` A.varray pos)
 (* /\
            log at position h0.pos contains a vali repr of v *)

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
