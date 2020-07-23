module Veritas.LogStream

(* From verifier/lstream.h:LogStream, utils/utils.h:LogStreamImpl *)

module B = LowStar.ConstBuffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module LP = LowParse.Low.Base

val read_t: Type0
val read_footprint (r: read_t) : GTot B.loc
val read_invariant (r: read_t) (h: HS.mem) : GTot Type0

val read_buffer (r: read_t) : GTot (B.const_buffer B.IMMUTABLE U8.t)
val read_cur (r: read_t) (h: HS.mem) : GTot U32.t

val read_create_from_buffer
  (b: B.const_buffer B.IMMUTABLE U8.t)
  (len: U32.t)
: HST.ST read_t
  (requires (fun h -> B.live h b))
  (ensures (fun h r h' ->
    B.fresh (read_footprint r) h h' /\
    read_invariant r h' /\
    read_cur r h' == 0ul /\
    read_buffer r == b
  ))

val read_end
  (r: read_t)
: HST.Stack bool
  (requires (fun h ->
    read_invariant r h
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    res == (read_cur r h = B.len (read_buffer r))
  ))

val read #k #t (#p: parser k t) (v: validator p) (l: leaf_reader p) (r: read_t) : HST.Stack (option t)
  (requires (fun h ->
    read_invariant r h
  ))
  (ensures (fun h res h' ->
    read_invariant r h' /\
    begin match res with
    | None ->
      (~ (LP.valid p h (read_buffer b) (read_cur b h))) /\
      B.modifies B.loc_none h h'
    | Some v ->
      LP.valid p h (read_buffer b) (read_cur b h) /\
      B.modifies (read_footprint r) h h' /\
      v == contents p h (read_buffer b) (read_cur b h) /\
      read_cur b h' == get_valid_pos p h (read_buffer b) (read_cur b h)
    end
  ))

val write_t: Type0
val write_footprint (w: write_t) (h: HS.mem) : GTot B.loc
val write_invariant (w: write_t) (h: HS.mem) : GTot Type0
val write_contents (w: write_t) (h: HS.mem) : GTot (Seq.seq U8.t)

val write #k #t (#p: parser k t) (#s: serializer p) (sz: size32 s) (l: leaf_writer_strong p) (v: t) (w: write_t) : HST.ST (option (Ghost.erased B.loc))
  (requires (fun h ->
    write_invariant w h
  ))
  (ensures (fun h res h' ->
    write_invariant w h' /\
    begin match res with
    | Some loc ->
      B.modifies (write_footprint w h) h h' /\
      B.fresh loc h h' /\ // maybe a new block allocated?
      write_footprint w h' == write_footprint w h `B.loc_union` loc /\
      write_contents w h' == write_contents w h `Seq.append` serialize s v
    | None ->
      B.modifies B.loc_none h h' /\
      Seq.length s v > block_size
    end
  ))
