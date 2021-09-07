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

inline_for_extraction
noextract
let bounded_u32 (l:nat) = x:U32.t { U32.v x <= l }

val extract_log_entry_from (len: U32.t)
                           (buf: B.lbuffer U8.t (U32.v len))
                           (pos: bounded_u32 (U32.v len))
  : HST.Stack (either (vlog_entry & bounded_u32 (U32.v len))
                  (bounded_u32 (U32.v len) & string))
          (requires fun h ->
            B.live h buf
          )
          (ensures fun h0 v h1 ->
            B.live h1 buf /\
            B.modifies B.loc_none h0 h1 /\
            begin match v with
            | Inl (v, pos') ->
              U32.v pos <= U32.v pos' /\
              parsed (Seq.slice (B.as_seq h0 buf) (U32.v pos) (U32.v pos')) v
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
