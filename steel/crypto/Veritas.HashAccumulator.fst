module Veritas.HashAccumulator

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
open LowStar.BufferOps

let initial_hash
  = Seq.create 32 0uy

let hash_value (s:Seq.seq U8.t { Seq.length s <= blake2_max_input_length })
  : hash_value_t
  = Hacl.Blake2b_32.spec s 0 Seq.empty 32


noextract inline_for_extraction
let xor_bytes (s1: Seq.seq U8.t)
              (s2: Seq.seq U8.t { S.length s1 == S.length s2 })
  : s3:Seq.seq U8.t { S.length s3 == S.length s1 }
  = S.init (S.length s1) (fun i -> S.index s1 i `FStar.UInt8.logxor` S.index s2 i)

let aggregate_hash_value (h0 h1: hash_value_t)
  : hash_value_t
  = xor_bytes h0 h1

let as_hash_value_pfx (b:hash_value_buf) (h:HS.mem) (n:nat { n <= 32 }) =
  Seq.slice (as_hash_value b h) 0 n

let state = hash_value_buf

let invariant s h = B.live h s /\ B.freeable s

let v_hash (s:state) (h:HS.mem)
  : GTot hash_value_t
  = as_hash_value s h

let footprint s = B.loc_addr_of_buffer s

let frame _ _ _ _ = ()

////////////////////////////////////////////////////////////////////////////////

(** Create an instance of a hash accumulator in the heap *)
let create_in () = B.malloc HS.root 0uy 32ul

////////////////////////////////////////////////////////////////////////////////
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

////////////////////////////////////////////////////////////////////////////////
let add s b l =
  let h0 = ST.get () in
  let b = B.sub b 0ul (Ghost.hide l) in
  assert (invariant s h0);
  push_frame ();
  let acc = s in
  let h1 = ST.get () in
  assert (invariant s h1);
  let tmp = B.alloca 0uy 32ul in
  assert_norm (64 + Hacl.Blake2b_32.size_block < pow2 32);
  assert_norm (64 < pow2 32);
  assert_norm (64 <= Hacl.Blake2b_32.max_key);
  let h1' = ST.get () in
  Hacl.Blake2b_32.blake2b 32ul tmp l b 0ul B.null;
  let h2 = ST.get () in
  assert (B.as_seq h1' B.null `Seq.equal` Seq.empty #U8.t);
  assert (B.as_seq h2 tmp == hash_value (B.as_seq h1 b));
  aggregate_hash_value_buf acc tmp;
  let h = ST.get () in
  assert (v_hash s h ==
                aggregate_hash_value (v_hash s h0)
                                     (hash_value (B.as_seq h0 b)));
  pop_frame ()

////////////////////////////////////////////////////////////////////////////////
let get s out = B.blit s 0ul out 0ul 32ul

////////////////////////////////////////////////////////////////////////////////
let free s = B.free s
