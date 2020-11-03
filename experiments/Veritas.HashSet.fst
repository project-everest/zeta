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
noeq
type state_s = {
  acc: acc:B.buffer u8 { B.length acc == 64 };
  seen: B.pointer (G.erased (list hashable_bytes));
  key: key:B.buffer u8 { B.length key == 64 };
  g_key: G.erased t_key;
}

let seen h s =
  let s = B.deref h s in
  G.reveal (B.deref h s.seen)

let v h s =
  let s = B.deref h s in
  B.as_seq h s.acc

let key s =
  G.reveal s.g_key

let footprint_s s =
  B.(loc_addr_of_buffer s.acc `loc_union` loc_addr_of_buffer s.seen `loc_union` loc_addr_of_buffer s.key)

let invariant_s h s =
  B.live h s.acc /\ B.freeable s.acc /\
  B.live h s.seen /\ B.freeable s.seen /\
  B.live h s.key /\ B.freeable s.key /\
  B.disjoint s.acc s.seen /\
  B.disjoint s.acc s.key /\
  B.disjoint s.seen s.key /\
  B.as_seq h s.acc == gfold_right (fold_and_hash s.g_key) (G.reveal (B.deref h s.seen)) zero /\
  G.reveal s.g_key == B.as_seq h s.key

let invariant_loc_in_footprint _ _ =
  allow_inversion state_s

let v_folds_seen _ _ =
  ()

let frame _ _ _ _ =
  allow_inversion state_s

#push-options "--ifuel 1 --fuel 1 --z3rlimit 50"
let create_in r k' =
  let h0 = ST.get () in
  let b = B.malloc r 0uy 64ul in
  let p = B.malloc r (G.hide ([] #hashable_bytes)) 1ul in
  let k = B.malloc r 0uy 64ul in
  B.blit k' 0ul k 0ul 64ul;
  let h1 = ST.get () in
  B.modifies_only_not_unused_in B.loc_none h0 h1;
  [@inline_let]
  let s: state_s = { acc = b; seen = p; key = k; g_key = B.as_seq h0 k' } in
  B.malloc r s 1ul
#pop-options

assume val xor_inplace (b1: B.buffer u8) (b2: B.buffer u8): Stack unit
  (requires (fun h0 ->
    B.live h0 b1 /\ B.live h0 b2 /\
    B.length b1 == B.length b2))
  (ensures (fun h0 _ h1 ->
    B.(modifies (loc_buffer b1) h0 h1) /\
    B.as_seq h1 b1 == xor_bytes (B.as_seq h0 b1) (B.as_seq h0 b2)))

#push-options "--fuel 1 --z3rlimit 200"
let add s b l =
  let _ = allow_inversion state_s in
  let h0 = ST.get () in
  assert (invariant h0 s);
  push_frame ();
  let { acc; seen; key } = !* s in
  let h1 = ST.get () in
  assert (invariant h1 s);
  let tmp = B.alloca 0uy 64ul in
  assert_norm (64 + Hacl.Blake2b_32.size_block < pow2 32);
  assert_norm (64 < pow2 32);
  assert_norm (64 <= Hacl.Blake2b_32.max_key);
  assert (B.length tmp == 64);
  Hacl.Blake2b_32.blake2b 64ul tmp l b 64ul key;
  xor_inplace acc tmp;
  seen *= G.hide (B.as_seq h1 b :: B.deref h1 seen);
  pop_frame ()
#pop-options

//let get s l =

let free s =
  let { seen; acc; key } = !* s in
  B.free s;
  B.free seen;
  B.free acc;
  B.free key
