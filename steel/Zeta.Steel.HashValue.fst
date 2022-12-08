module Zeta.Steel.HashValue
open Steel.ST.Util
open Zeta.Steel.Util
module P = Zeta.Steel.Parser
module T = Zeta.Steel.FormatsManual
module Blake = Hacl.Hash.Blake2b_256
module A = Steel.ST.Array
module U8 = FStar.UInt8
module LE = Zeta.Steel.LogEntry
module R = Steel.ST.Reference
module G = Zeta.Steel.Globals

let bytes_as_u256 (b:Seq.seq U8.t { Seq.length b == 32 })
  : GTot T.u256
  = LE.spec_parser_u256_never_fails b;
    let Some (v, _) = LE.spec_parser_u256 b in
    v

let hashfn (v:T.value)
  : GTot T.hash_value
  = let bytes = LE.spec_serializer_value v in
    let hash_bytes = Blake.spec bytes G.blake_key_len G.blake_key 32 in
    bytes_as_u256 hash_bytes

[@@CAbstractStruct]
noeq
type hasher_t = {
  serialization_buffer: (a: A.larray U8.t 4096 { A.is_full_array a });
  hash_buffer: (a: A.larray U8.t 32 { A.is_full_array a });
  dummy: (a:A.array U8.t { A.is_full_array a })
}

[@@__steel_reduce__; __reduce__]
let inv (h:hasher_t) =
  exists_ (array_pts_to h.hash_buffer) `star`
  exists_ (array_pts_to h.serialization_buffer) `star`
  exists_ (array_pts_to h.dummy)

let alloc (_:unit)
  : STT hasher_t emp inv
  = let hb = A.alloc 0uy 32sz in
    intro_exists _ (array_pts_to hb);
    let sb = A.alloc 0uy 4096sz in
    intro_exists _ (array_pts_to sb);
    let dummy = A.alloc 0uy 1sz in
    let res = {
      serialization_buffer = sb;
      hash_buffer = hb;
      dummy = dummy;
    } in
    rewrite (exists_ (array_pts_to sb))
            (exists_ (array_pts_to res.serialization_buffer));
    rewrite (exists_ (array_pts_to hb))
            (exists_ (array_pts_to res.hash_buffer));
    rewrite (exists_ (array_pts_to dummy))
            (exists_ (array_pts_to res.dummy));
    return res

let array_free (a:A.array 'a)
  : ST unit (exists_ (array_pts_to a)) (fun _ -> emp) (A.is_full_array a) (fun _ -> True)
  = let v = elim_exists () in
    intro_exists_erased v (A.pts_to a full_perm);
    A.free a

let free (h:hasher_t)
  : STT unit (inv h) (fun _ -> emp)
  = array_free h.hash_buffer;
    array_free h.serialization_buffer;
    array_free h.dummy

let read_hash_u256 (#hv:Ghost.erased _)
                   (hb:A.larray U8.t 32)
  : ST T.u256
    (A.pts_to hb full_perm hv)
    (fun _ -> A.pts_to hb full_perm hv)
    (requires True)
    (ensures fun res ->
      Seq.length hv == 32 /\
      res == bytes_as_u256 hv)
  = A.pts_to_length hb _;
    LE.spec_parser_u256_never_fails hv;
    let res = LE.parser_u256 32ul 0ul 32ul hb in
    let Some (v, _) = res in
    return v


let get_blake_key (_:unit)
  : STGhostT perm Set.empty
      emp
      (fun p -> A.pts_to G.blake_key_buffer p G.blake_key)
  =  let open G in
     let body (_:unit)
       : STGhostT perm (add_inv Set.empty blake_key_inv)
           (exists_ (fun p -> A.pts_to blake_key_buffer p blake_key) `star` emp)
           (fun q -> exists_ (fun p -> A.pts_to blake_key_buffer p blake_key) `star` 
                  A.pts_to blake_key_buffer q blake_key)
       = let p = elim_exists () in
         A.share G.blake_key_buffer p (half_perm p) (half_perm p);
         intro_exists (half_perm p) (fun p -> A.pts_to blake_key_buffer p blake_key);
         half_perm p
     in
     with_invariant_g blake_key_inv body

// val blake2b 
//     (#sout:Ghost.erased (Seq.seq U8.t))
//     (#in_p:perm)
//     (#in_v:Ghost.erased (Seq.seq U8.t))
//     (nn:size_t{1 <= UInt32.v nn /\ UInt32.v nn <= max_output})
//     (output: A.array U8.t)
//     (ll: size_t)
//     (input: A.array U8.t { U32.v ll <= Seq.length in_v })
//     (kk: size_t { U32.v kk <= 64 })
//     (#k_p:perm)
//     (#k_v:Ghost.erased (Seq.seq U8.t) { Seq.length k_v == U32.v kk })
//     (key: A.array U8.t)
//  : ST unit
//     (A.pts_to output full_perm sout `star`
//      A.pts_to input in_p in_v `star`
//      A.pts_to key k_p k_v)
//     (fun _ -> 
//       A.pts_to output full_perm
//                (spec (Seq.slice in_v 0 (U32.v ll))
//                      0
//                      Seq.empty
//                      (UInt32.v nn)) `star`
//       A.pts_to input in_p in_v `star`
//       A.pts_to key k_p k_v)
//   (requires
//     A.length output = U32.v nn)
//   (ensures fun _ ->
//     True)

//TODO: Not sure why this proof takes so long
#push-options "--fuel 0 --ifuel 1 --z3rlimit_factor 10"
let hash_value (h:hasher_t)
               (v:T.value)
  : ST T.hash_value
    (inv h)
    (fun _ -> inv h)
    (requires True)
    (ensures fun res -> hashfn v == res)
  = let n = LE.serialize_value 4096ul 0ul h.serialization_buffer v in
    let hv = elim_exists  #_ #_ #(array_pts_to h.hash_buffer) () in
    let sv = elim_exists () in
    elim_pure _;
    A.pts_to_length h.hash_buffer _;
    let _ = get_blake_key () in
    Blake.blake2b 32ul h.hash_buffer n h.serialization_buffer 32ul G.blake_key_buffer;
    let res = read_hash_u256 h.hash_buffer in
    intro_exists _ (array_pts_to h.serialization_buffer);
    intro_exists _ (array_pts_to h.hash_buffer);
    drop (A.pts_to G.blake_key_buffer _ _);
    return res
#pop-options
