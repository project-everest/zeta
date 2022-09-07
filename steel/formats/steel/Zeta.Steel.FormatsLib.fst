module Zeta.Steel.FormatsLib

(* This is a transitional module to quickly implement inefficient Steel parsers from "intermediate-level" parsers based on FStar.Bytes. *)

module LP = LowParse.SLow.Base
module P = Zeta.Steel.Parser
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module S = Steel.ST.Util
module A = Steel.ST.Array

let rec read_bytes
    (len: Ghost.erased U32.t)
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

let rec write_bytes
    (alen: Ghost.erased U32.t)
    (offset:U32.t)
    (b: Ghost.erased (Seq.seq U8.t))
    (new_bytes: FStar.Bytes.bytes)
    (a:A.array U8.t)
    (sq: squash (
      U32.v offset + FStar.Bytes.length new_bytes <= Seq.length b /\
      Seq.length b == U32.v alen
    ))
:   S.ST (Ghost.erased (Seq.seq U8.t))
       (A.pts_to a Steel.FractionalPermission.full_perm b)
       (fun b' -> A.pts_to a Steel.FractionalPermission.full_perm b')
       (requires True)
       (ensures fun b' ->
         let offset' = U32.v offset + FStar.Bytes.length new_bytes in
         Seq.length b' == Seq.length b /\
         (forall (i: nat { i < Seq.length b }) . {:pattern Seq.index b' i}
           Seq.index b' i == (if U32.v offset <= i && i < offset' then FStar.Bytes.index new_bytes (i - U32.v offset) else Seq.index b i))
       )
=
  let len = FStar.Bytes.len new_bytes in
  if len = 0ul
  then
    S.return b
  else begin
    let r = FStar.Bytes.get new_bytes 0ul in
    A.write a offset r;
    write_bytes alen (offset `U32.add` 1ul) (Seq.upd b (U32.v offset) r) (FStar.Bytes.sub new_bytes 1ul (len `U32.sub` 1ul)) a ()
  end

let mk_steel_serializer
  (#k: LP.parser_kind)
  (#t: Type)
  (#p: LP.parser k t)
  (#s: LP.serializer p)
  (s32: LP.serializer32 s)
  (#p0: P.spec_parser t)
  (s0: P.spec_serializer p0)
  (s0_eq: squash (forall (x: t) . s0 x `Seq.equal` s x))
: Tot (P.serializer s0)
= fun len offset a v ->
  let new_bytes = s32 v in
  let slice_len = FStar.Bytes.len new_bytes in
  let b : Ghost.erased (Seq.seq P.byte) = S.elim_exists #_ #_ #(Zeta.Steel.Util.array_pts_to a) () in
  A.pts_to_length #_ #_ #Steel.FractionalPermission.full_perm a b;
  let b' : Ghost.erased (Seq.seq P.byte) = write_bytes len offset b new_bytes a () in
  assert (s0 v `Seq.equal` P.slice b' offset slice_len);
  S.intro_pure _;
  S.intro_exists_erased b' (fun (bs: Seq.seq P.byte) ->
              Zeta.Steel.Util.array_pts_to a bs `S.star`
              S.pure (
                U32.v slice_len == Seq.length (s0 v) /\
                P.len_offset_slice_ok a len offset slice_len /\
                Seq.length bs == (U32.v len <: nat) /\
                s0 v == P.slice bs offset slice_len ));
  S.return slice_len
