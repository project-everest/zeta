module Zeta.Steel.FormatsLib

(* This is a transitional module to quickly implement inefficient Steel parsers from "intermediate-level" parsers based on FStar.Bytes. *)

module LP = LowParse.SLow.Base
module P = Zeta.Steel.Parser
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module S = Steel.ST.Util
module A = Steel.ST.Array

let rec read_bytes
    (len:U32.t)
    (offset:U32.t)
    (slice_len:U32.t)
    (#b: Ghost.erased (Seq.seq U8.t) { Seq.length b == U32.v len })
    (a:A.array U8.t)
    (p: _)
    (sq: squash (P.len_offset_slice_ok a len offset slice_len))
:   S.ST FStar.Bytes.bytes
       (A.pts_to a p b)
       (fun _ -> A.pts_to a p b)
       (requires True)
       (ensures fun o ->
         FStar.Bytes.reveal o `Seq.equal` P.slice b offset slice_len
       )
= if slice_len = 0ul
  then S.return FStar.Bytes.empty_bytes
  else
    let x = A.read a offset in
    let tail = read_bytes len (offset `U32.add` 1ul) (slice_len `U32.sub` 1ul) #b a _ () in
    FStar.Bytes.append (FStar.Bytes.create 1ul x) tail

let mk_steel_parser
  (#k: LP.parser_kind)
  (#t: Type)
  (#p: LP.parser k t)
  (p32: LP.parser32 p)
  (p0: P.spec_parser t)
  (p0_eq: squash (forall x . Zeta.Formats.Lib.bare_parser_of_spec_parser p0 x == p x ))
: Tot (P.parser p0)
= fun len offset slice_len a ->
  let b = read_bytes len offset slice_len a _ () in
  p32 b
