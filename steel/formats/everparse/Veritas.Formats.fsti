module Veritas.Formats
include Veritas.Formats.Pure
include Veritas.Formats.Types

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

val serialize_value: v:value -> dst: B.lbuffer U8.t (U32.v (serialize_length v)) ->
  HST.Stack unit
    (requires fun h -> B.live h dst)
    (ensures fun h0 _ h1 -> B.(modifies (loc_buffer dst) h0 h1))

val extract_log_entry_from (len: U32.t) (buf: B.lbuffer U8.t (U32.v len)) (pos: B.pointer (x: U32.t { U32.v x <= U32.v len }))
  : HST.Stack (option vlog_entry)
          (requires fun h ->
            B.live h buf /\ B.live h pos /\ B.disjoint buf pos
          )
          (ensures fun h0 v h1 ->
            let p = B.deref h0 pos in
            let p' = B.deref h1 pos in
            B.live h1 buf /\ B.live h1 pos /\ B.disjoint buf pos /\
            B.modifies (B.loc_buffer pos) h0 h1 /\
            U32.v p <= U32.v p' /\
            begin match v with
            | Some v ->
              parsed (Seq.slice (B.as_seq h0 buf) (U32.v p) (U32.v p')) v
            | _ -> True
            end
          )

val serialize_stamped_record
  (dst: B.buffer U8.t)
  (r: stamped_record)
: HST.Stack U32.t
  (requires (fun h -> B.live h dst /\ 184 <= B.length dst))
  (ensures (fun h0 len h1 ->
    U32.v len <= B.length dst /\
    B.modifies (B.loc_buffer (B.gsub dst 0ul len)) h0 h1
  ))
