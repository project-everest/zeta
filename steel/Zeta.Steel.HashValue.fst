module Zeta.Steel.HashValue
open Steel.ST.Util
open Zeta.Steel.Util
module P = Zeta.Steel.Parser
module T = Zeta.Steel.FormatsManual
module Blake = Hacl.Blake2b_32
module A = Steel.ST.Array
module U8 = FStar.UInt8

assume
val spec_parser_value: P.spec_parser T.value

assume
val spec_serializer_value: P.spec_serializer spec_parser_value

assume
val serialize_value : P.serializer spec_serializer_value

/// This is an ad hoc bound due to a bound on Blake hashable inputs
assume
val serialized_value_length (s:T.value)
  : Lemma  (Seq.length (spec_serializer_value s) <= 4096)
           [SMTPat (Seq.length (spec_serializer_value s))]

let bytes_as_u256 (b:Seq.seq U8.t { Seq.length b == 32 })
  : GTot T.u256
  = let u64s = FStar.Endianness.seq_uint64_of_le 4 b in
    { v0 = Seq.index u64s 0;
      v1 = Seq.index u64s 1;
      v2 = Seq.index u64s 2;
      v3 = Seq.index u64s 3 }

let hashfn (v:T.value)
  : GTot T.hash_value
  = let bytes = spec_serializer_value v in
    let hash_bytes = Blake.spec bytes 0 Seq.empty 32 in
    bytes_as_u256 hash_bytes

noeq
type hasher_t = {
  serialization_buffer: A.larray U8.t 4096;
  hash_buffer: A.larray U8.t 32
}

[@@__steel_reduce__; __reduce__]
let inv (h:hasher_t) =
  exists_ (array_pts_to h.hash_buffer) `star`
  exists_ (array_pts_to h.serialization_buffer)

let alloc (_:unit)
  : STT hasher_t emp inv
  = let hb = A.alloc 0uy 32ul in
    intro_exists _ (array_pts_to hb);
    let sb = A.alloc 0uy 4096ul in
    intro_exists _ (array_pts_to sb);
    let res = {
      serialization_buffer = sb;
      hash_buffer = hb
    } in
    rewrite (exists_ (array_pts_to sb))
            (exists_ (array_pts_to res.serialization_buffer));
    rewrite (exists_ (array_pts_to hb))
            (exists_ (array_pts_to res.hash_buffer));
    return res

let array_free (a:A.array 'a)
  : STT unit (exists_ (array_pts_to a)) (fun _ -> emp)
  = let v = elim_exists () in
    intro_exists_erased v (A.pts_to a full_perm);
    A.free a

let free (h:hasher_t)
  : STT unit (inv h) (fun _ -> emp)
  = array_free h.hash_buffer;
    array_free h.serialization_buffer

let read_hash_u256 (#hv:Ghost.erased _)
                   (hb:A.larray U8.t 32)
  : ST T.u256
    (A.pts_to hb full_perm hv)
    (fun _ -> A.pts_to hb full_perm hv)
    (requires True)
    (ensures fun res ->
      Seq.length hv == 32 /\
      res == bytes_as_u256 hv)
  = admit__()

let hash_value (h:hasher_t)
               (v:T.value)
  : ST T.hash_value
    (inv h)
    (fun _ -> inv h)
    (requires True)
    (ensures fun res -> hashfn v == res)
  = let n = serialize_value 4096ul 0ul h.serialization_buffer v in
    let hv = elim_exists  #_ #_ #(array_pts_to h.hash_buffer) () in
    let sv = elim_exists () in
    elim_pure _;
    A.pts_to_length h.hash_buffer _;
    Blake.blake2b 32ul h.hash_buffer n h.serialization_buffer;
    let res = read_hash_u256 h.hash_buffer in
    intro_exists _ (array_pts_to h.serialization_buffer);
    intro_exists _ (array_pts_to h.hash_buffer);
    return res
