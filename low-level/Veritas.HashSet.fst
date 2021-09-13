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

let hash_value_t = Hacl.Blake2b_32.lbytes 32
let hash_value_buf = B.lbuffer u8 32

// Relying on a somewhat recent kremlin optimization that removes pointers to unit
noeq
type state_s = {
  acc: hash_value_buf;
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

unfold
let invariant_s' h s =
  B.live h s.acc /\ B.freeable s.acc /\
  B.live h s.seen /\ B.freeable s.seen /\
  B.live h s.key /\ B.freeable s.key /\
  B.disjoint s.acc s.seen /\
  B.disjoint s.acc s.key /\
  B.disjoint s.seen s.key /\
  B.as_seq h s.acc == gfold_right (fold_and_hash s.g_key) (G.reveal (B.deref h s.seen)) zero /\
  G.reveal s.g_key == B.as_seq h s.key /\
  B.as_seq h s.key `Seq.equal` Seq.create 64 0uy

let invariant_s = invariant_s'

let invariant_loc_in_footprint _ _ =
  allow_inversion state_s

let v_folds_seen _ _ =
  ()

let frame _ _ _ _ =
  allow_inversion state_s

#push-options "--ifuel 1 --fuel 1 --z3rlimit 50"
let create_in r =
  let b = B.malloc r 0uy 32ul in
  let p = B.malloc r (G.hide ([] #hashable_bytes)) 1ul in
  let k = B.malloc r 0uy 64ul in
  let h0 = ST.get () in
  [@inline_let]
  let s: state_s = { acc = b; seen = p; key = k; g_key = B.as_seq h0 k } in
  B.malloc r s 1ul
#pop-options


let hash_value (s:Seq.seq U8.t { Seq.length s <= blake2_max_input_length })
  : hash_value_t
  = Hacl.Blake2b_32.spec s 64 (Seq.create 64 0uy) 32

let aggregate_hash_value (h0 h1: hash_value_t)
  : hash_value_t
  = xor_bytes h0 h1

let as_hash_value (b:hash_value_buf) (h:HS.mem) =
  B.as_seq h b

let as_hash_value_pfx (b:hash_value_buf) (h:HS.mem) (n:nat { n <= 32 }) =
  Seq.slice (as_hash_value b h) 0 n

val aggregate_hash_value_buf (b1: hash_value_buf) (b2: hash_value_buf)
  : Stack unit
    (requires fun h0 ->
      B.live h0 b1 /\
      B.live h0 b2 /\
      B.disjoint b1 b2)
    (ensures fun h0 _ h1 ->
      B.(modifies (loc_buffer b1) h0 h1) /\
      as_hash_value b1 h1 == aggregate_hash_value (as_hash_value b1 h0)
                                                  (as_hash_value b2 h0))
let aggregate_hash_value_buf b1 b2 =
  let h0 = ST.get () in
  let inv h (i:nat) =
      let s1 = B.as_seq h0 b1 in
      let s2 = B.as_seq h0 b2 in
      i <= 32 /\
      B.live h b1 /\
      B.live h b2 /\
      Seq.slice (B.as_seq h b1) i 32 `Seq.equal` Seq.slice s1 i 32 /\
      B.modifies (B.loc_buffer b1) h0 h /\
      as_hash_value_pfx b1 h i `Seq.equal`
      xor_bytes (Seq.slice s1 0 i) (Seq.slice s2 0 i)
  in
  let extend_inv (h:HS.mem) (i:nat) (h':HS.mem)
    : Lemma
      (requires
        inv h i /\
        i < 32 /\
        B.as_seq h' b1 ==
        Seq.upd (B.as_seq h b1)
                i
                (U8.logxor
                  (B.get h b1 i)
                  (B.get h b2 i)))
      (ensures (
        let s1 = B.as_seq h0 b1 in
        let s2 = B.as_seq h0 b2 in
        as_hash_value_pfx b1 h' (i + 1) `Seq.equal`
        xor_bytes (Seq.slice s1 0 (i + 1))
                  (Seq.slice s2 0 (i + 1)) /\
        Seq.slice (B.as_seq h' b1) (i + 1) 32 `Seq.equal`
        Seq.slice s1 (i + 1) 32))
    = let s1 = B.as_seq h0 b1 in
      let s2 = B.as_seq h0 b2 in
      let s1_h =  B.as_seq h b1 in
      let s1_h' = B.as_seq h' b1 in
      assert (as_hash_value_pfx b1 h' (i + 1) `Seq.equal`
              Seq.snoc (as_hash_value_pfx b1 h i)
                       (Seq.index s1_h' i));
      assert (xor_bytes (Seq.slice s1 0 (i + 1))
                        (Seq.slice s2 0 (i + 1)) `Seq.equal`
              Seq.snoc
                 (xor_bytes (Seq.slice s1 0 i)
                            (Seq.slice s2 0 i))
                 (U8.logxor (Seq.index s1 i) (Seq.index s2 i)));
      assert (Seq.index (B.as_seq h b2) i == Seq.index s2 i);
      assert (Seq.slice (B.as_seq h b1) i 32 == Seq.slice s1 i 32);
      Seq.lemma_index_slice s1 i 32 0;
      assert (Seq.index (B.as_seq h b1) i == Seq.index s1 i);
      assert ((Seq.index s1_h' i) ==
                 (U8.logxor (Seq.index s1 i) (Seq.index s2 i)));
      assert (Seq.slice s1 (i + 1) 32 `Seq.equal` Seq.tail (Seq.slice s1 i 32));
      assert (Seq.slice (B.as_seq h' b1) (i + 1) 32 `Seq.equal`
               Seq.tail (Seq.slice (B.as_seq h' b1) i 32));
      assert (Seq.slice (B.as_seq h' b1) (i + 1) 32 `Seq.equal`
              Seq.slice s1 (i + 1) 32)
  in
  [@@inline_let]
  let body (i:U32.t { U32.v i < 32 })
    : Stack unit
      (fun h -> inv h (U32.v i))
      (fun h0 _ h1 -> inv h1 (U32.v i + 1))
    = let h = ST.get () in
      let v1 = B.index b1 i in
      let v2 = B.index b2 i in
      B.upd b1 i (U8.logxor v1 v2);
      let h' = ST.get () in
      extend_inv h (U32.v i) h'
  in
  assert (inv h0 0);
  let _ =
    C.Loops.for 0ul 32ul inv body
  in
  let h = ST.get () in
  assert (inv h 32);
  assert (Seq.slice (B.as_seq h0 b1) 0 32 `Seq.equal` (B.as_seq h0 b1));
  assert (Seq.slice (B.as_seq h0 b2) 0 32 `Seq.equal` (B.as_seq h0 b2));
  B.gsub_zero_length b1;
  assert (B.gsub b1 0ul 32ul == b1);
  assert (as_hash_value b1 h ==
          aggregate_hash_value (as_hash_value b1 h0) (as_hash_value b2 h0))

let v_hash (s:state) (h:HS.mem)
  : GTot hash_value_t
  = as_hash_value (B.get h s 0).acc h

#push-options "--fuel 1 --z3rlimit 20 --query_stats"
let add s b l =
  let _ = allow_inversion state_s in
  let h0 = ST.get () in
  let b = B.sub b 0ul (Ghost.hide l) in
  assert (invariant h0 s);
  push_frame ();
  let s0 = !* s in
  let { acc; seen; key } = s0 in
  let h1 = ST.get () in
  assert (invariant h1 s);
  let tmp = B.alloca 0uy 32ul in
  assert_norm (64 + Hacl.Blake2b_32.size_block < pow2 32);
  assert_norm (64 < pow2 32);
  assert_norm (64 <= Hacl.Blake2b_32.max_key);
  Hacl.Blake2b_32.blake2b 32ul tmp l b 64ul key;
  let h2 = ST.get () in
  assert (B.as_seq h2 tmp == hash_value (B.as_seq h1 b));
  aggregate_hash_value_buf acc tmp;
  seen *= G.hide (B.as_seq h1 b :: B.deref h1 seen);
  let h = ST.get () in
  assert (v_hash s h ==
                aggregate_hash_value (v_hash s h0)
                                     (hash_value (B.as_seq h0 b)));
  pop_frame ()
#pop-options

let get s =
  let s = !*s in
  let hash0 = B.sub s.acc 0ul 8ul in
  let hash1 = B.sub s.acc 8ul 8ul in
  let hash2 = B.sub s.acc 16ul 8ul in
  let hash3 = B.sub s.acc 24ul 8ul in
  let v0 = LowStar.Endianness.load64_le hash0 in
  let v1 = LowStar.Endianness.load64_le hash1 in
  let v2 = LowStar.Endianness.load64_le hash2 in
  let v3 = LowStar.Endianness.load64_le hash3 in
  { Veritas.Formats.Types.v0; Veritas.Formats.Types.v1; Veritas.Formats.Types.v2; Veritas.Formats.Types.v3 }

let free s =
  let { seen; acc; key } = !* s in
  B.free s;
  B.free seen;
  B.free acc;
  B.free key
