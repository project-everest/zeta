module Veritas.Formats
include Veritas.Formats.Aux
include Veritas.Formats.Types

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

let bool_of_vbool (x: vbool) : Tot bool =
  match x with
  | Vfalse -> false
  | Vtrue -> true

let vbool_of_bool (x: bool) : Tot vbool =
  if x then Vtrue else Vfalse

val serialize_length : value -> (l: U32.t { U32.v l > 0 })

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
            B.live h1 buf /\ B.live h1 pos /\ B.disjoint buf pos /\
            B.modifies (B.loc_buffer buf `B.loc_union` B.loc_buffer pos) h0 h1) (* /\
            log at position h0.pos contains a vali repr of v *)

val serialize_stamped_record
  (dst: B.buffer U8.t)
  (r: stamped_record)
: HST.Stack U32.t
  (requires (fun h -> B.live h dst /\ 181 <= B.length dst))
  (ensures (fun h0 len h1 ->
    U32.v len <= B.length dst /\
    B.modifies (B.loc_buffer (B.gsub dst 0ul len)) h0 h1
  ))
