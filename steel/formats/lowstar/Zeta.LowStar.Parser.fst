module Zeta.LowStar.Parser
include Zeta.Steel.Parser

module B = LowStar.Buffer
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32

let byte_array = B.buffer byte

let len_offset_slice_ok (a:byte_array)
                        (len offset slice_len:U32.t) =
  B.length a == U32.v len /\
  U32.v offset + U32.v slice_len <= B.length a

let parser (#t:Type0) (p:spec_parser t) =
    len:U32.t ->
    offset:U32.t ->
    slice_len:U32.t ->
    a:byte_array { len_offset_slice_ok a len offset slice_len } ->
    HST.Stack (option (t & U32.t))
       (requires fun h ->
         B.live h a
       )
       (ensures fun h o h' ->
         let b = B.as_seq h a in
         B.modifies B.loc_none h h' /\
         begin match p (slice b offset slice_len), o with
         | None, None -> True
         | Some (x, n), Some (y, n') -> x == y /\ n == U32.v n'
         | _ -> False
         end
       )
