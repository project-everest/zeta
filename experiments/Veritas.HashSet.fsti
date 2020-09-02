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

inline_for_extraction noextract
val flush_interleaving: unit

noextract inline_for_extraction
let u8 = Lib.IntTypes.uint8

noextract inline_for_extraction
let bytes = S.seq u8

// JP: not being agile over the hash algorithm for the moment, can be improved later
let hashable_bytes = b:bytes { S.length b <= Spec.Hash.Definitions.(max_input_length SHA2_256) }

// ---


[@CAbstractStruct]
val state_s: Type0

let state = B.pointer state_s

// ---

val seen: h:HS.mem -> s:state -> GTot (list hashable_bytes)

let t = Spec.Hash.Definitions.(bytes_hash SHA2_256)

let zero: hashable_bytes =
  assert_norm (32 < pow2 61);
  S.create 32 (Lib.IntTypes.u8 0)

val v: h:HS.mem -> s:state -> GTot t

/// "As we all know", right folds are the easiest to work with because they
/// follow the natural structure of recursion (left-folds are evil).
///
/// JP: is this defined somewhere?
let rec gfold_right #a #b (f: b -> a -> GTot b) (xs: list a) (acc: b): Ghost b
  (requires True)
  (ensures fun _ -> True)
  (decreases xs)
=
  let _ = allow_inversion (list a) in
  match xs with
  | [] -> acc
  | x :: xs -> f (gfold_right f xs acc) x

/// JP: is this defined somewhere?
let xor_bytes (s1: bytes) (s2: bytes { S.length s1 == S.length s2 }): s3:bytes { S.length s3 == S.length s1 } =
  S.init (S.length s1) (fun i -> S.index s1 i `Lib.IntTypes.logxor` S.index s2 i)

let xor_bytes_commutative (s1: bytes) (s2: bytes { S.length s1 == S.length s2 }): Lemma
  (ensures xor_bytes s1 s2 == xor_bytes s2 s1)
  [ SMTPat (xor_bytes s1 s2) ]
=
  admit ()

let fold_and_hash (acc: t) (b: hashable_bytes) =
  xor_bytes Spec.Agile.Hash.(hash SHA2_256 b) acc

// ---

val footprint_s (s: state_s): GTot B.loc

let footprint (h: HS.mem) (s: state) =
  B.(loc_union (loc_addr_of_buffer s) (footprint_s (B.deref h s)))

let loc_includes_union_l_footprint_s
  (l1 l2: B.loc) (s: state_s)
: Lemma
  (requires (
    B.loc_includes l1 (footprint_s s) \/ B.loc_includes l2 (footprint_s s)
  ))
  (ensures (B.loc_includes (B.loc_union l1 l2) (footprint_s s)))
  [SMTPat (B.loc_includes (B.loc_union l1 l2) (footprint_s s))]
= B.loc_includes_union_l l1 l2 (footprint_s s)

val invariant_s (h: HS.mem) (s: state_s): Type0

// JP: bolting in the fact that we only heap-allocate this state
let invariant (h: HS.mem) (s: state) =
  invariant_s h (B.deref h s) /\
  B.live h s /\
  B.freeable s /\
  B.(loc_disjoint (loc_addr_of_buffer s) (footprint_s (B.deref h s)))

val invariant_loc_in_footprint
  (h: HS.mem)
  (s: state)
: Lemma
  (requires (invariant h s))
  (ensures (B.loc_in (footprint h s) h))
  [SMTPat (invariant h s)]

// ---

val v_folds_seen (h: HS.mem) (s: state): Lemma
  (requires (
    invariant h s))
  (ensures (
    v h s == gfold_right fold_and_hash (seen h s) zero))
  [ SMTPat (invariant h s) ]

val frame: l:B.loc -> s:state -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant h0 s /\
    B.loc_disjoint l (footprint h0 s) /\
    B.modifies l h0 h1))
  (ensures (
    invariant h1 s /\
    footprint h0 s == footprint h1 s /\
    v h0 s == v h1 s /\
    seen h0 s == seen h1 s))
  [ SMTPat (invariant h1 s); SMTPat (B.modifies l h0 h1) ]

// ---

val create_in: r:HS.rid -> ST state
  (requires (fun h0 ->
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    invariant h1 s /\
    seen h1 s == [] /\
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint h1 s) h0 h1 /\
    B.(loc_includes (loc_region_only true r) (footprint h1 s))))

val add: s:state -> b:B.buffer u8 -> l:U32.t -> Stack unit
  (requires (fun h0 ->
    invariant h0 s /\
    B.len b == l /\
    B.live h0 b /\
    B.length b <= Spec.Hash.Definitions.(max_input_length SHA2_256)))
  (ensures (fun h0 _ h1 ->
    invariant h1 s /\
    B.modifies (footprint_s (B.deref h0 s)) h0 h1 /\
    // FYI, no need to talk about a preserved footprint since I used footprint_s
    // which is not heap-dependent
    seen h1 s == B.as_seq h0 b :: seen h0 s))

val free: s:state -> ST unit
  (requires (fun h0 ->
    invariant h0 s))
  (ensures (fun h0 _ h1 ->
    B.modifies (footprint h0 s) h0 h1))
