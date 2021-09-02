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

module R = Steel.Reference

let bounded_u32 (l:nat) = x:U32.t { U32.v x <= l }

let larray t (l:U32.t) = a:A.array t { A.length a == U32.v l }

val valid_entry (s:Seq.seq U8.t) (from:nat) (to:nat) (e:vlog_entry) : prop

val extract_log_entry_from (len: U32.t)
                           (buf: larray U8.t len)
                           (pos: R.ref (bounded_u32 (U32.v len)))
  : Steel (option vlog_entry)
    (A.varray buf `star` R.vptr pos)
    (fun _ -> A.varray buf `star` R.vptr pos)
    (requires fun _ -> True)
    (ensures fun h0 x h1 ->
      A.asel buf h0 == A.asel buf h1 /\
      (match x with
       | None -> True
       | Some e ->
         valid_entry (A.asel buf h0) (U32.v (R.sel pos h0)) (U32.v (R.sel pos h1)) e))

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
