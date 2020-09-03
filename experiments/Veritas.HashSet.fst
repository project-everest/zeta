module Veritas.HashSet

#set-options "--fuel 0 --ifuel 0"

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost
module S = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

open FStar.HyperStack.ST

let flush_interleaving = ()

// ---

open LowStar.BufferOps

// Relying on a somewhat recent kremlin optimization that removes pointers to unit
let state_s =
  Hacl.Hash.Definitions.hash_t Spec.Hash.Definitions.SHA2_256 & B.pointer (G.erased (list hashable_bytes))

let seen h s =
  let _, p = B.deref h s in
  G.reveal (B.deref h p)

let v h s =
  let b, _ = B.deref h s in
  B.as_seq h b

let footprint_s (b, p) =
  B.(loc_addr_of_buffer b `loc_union` loc_addr_of_buffer p)

let invariant_s h (b, p) =
  B.live h b /\ B.freeable b /\
  B.live h p /\ B.freeable p /\
  B.as_seq h b == gfold_right fold_and_hash (G.reveal (B.deref h p)) zero /\
  B.disjoint b p

let invariant_loc_in_footprint _ _ =
  allow_inversion state_s

let v_folds_seen _ _ =
  ()

let frame _ _ _ _ =
  allow_inversion state_s

#push-options "--ifuel 1 --fuel 1 --z3rlimit 50"
let create_in r =
  let b = B.malloc r (Lib.IntTypes.u8 0) 32ul in
  let p = B.malloc r (G.hide []) 1ul in
  B.malloc r (b, p) 1ul
#pop-options

assume val xor_inplace (b1: B.buffer u8) (b2: B.buffer u8): Stack unit
  (requires (fun h0 ->
    B.live h0 b1 /\ B.live h0 b2 /\
    B.length b1 == B.length b2))
  (ensures (fun h0 _ h1 ->
    B.(modifies (loc_buffer b1) h0 h1) /\
    B.as_seq h1 b1 == xor_bytes (B.as_seq h0 b1) (B.as_seq h0 b2)))

#push-options "--fuel 1 --z3rlimit 100"
let add s b l =
  let _ = allow_inversion state_s in
  let h0 = ST.get () in
  assert (invariant h0 s);
  push_frame ();
  let acc, p = !* s in
  let h1 = ST.get () in
  assert (invariant h1 s);
  let tmp = B.alloca (Lib.IntTypes.u8 0) 32ul in
  Hacl.Hash.SHA2.hash_256 b l tmp;
  xor_inplace acc tmp;
  p *= G.hide (B.as_seq h1 b :: B.deref h1 p);
  pop_frame ()
#pop-options

let free s =
  let acc, p = !* s in
  B.free s;
  B.free acc;
  B.free p
