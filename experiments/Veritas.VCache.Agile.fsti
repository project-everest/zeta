module Veritas.VCache.Agile

module B = LowStar.Buffer
module HS = FStar.HyperStack

open FStar.HyperStack.ST

module VerifierTraits = Veritas.VerifierTraits
module VCell = Veritas.VCell

/// Based on veritas/verifier/vcache.h
///
/// The vcache is a vector of entries (i.e. a dynamically-sized array of size
/// ``CacheSize``, called ``_entries``), where each entry holds a slot. A slot
/// is an array of 20 64-bit integers; when cast to raw bytes, this is enough
/// space to hold either a MerkleLeafVCell or a MerkleInternalVCell. In C++,
/// clients of the VCache call its API to obtain a pointer to a raw slot
/// (pointer to bytes, via std::array.data), then proceed to call a placement
/// constructor to allocate an object at that location.
///
/// In Low*, we go for something much simpler: we introduce a data type that is
/// either a MerkleLeaf or a MerkleInternal. We know that KreMLin will compile
/// this to a tagged union, whose size will be the greater of the two, meaning
/// we implement the cache simply as an array of ``slot``.
///
/// This module, like the rest of the verified Veritas development, is agile
/// over the verifier traits, a set of compile-time parameters used to
/// specialize the code for e.g. a given cell implementation or hash algorithm.
/// See Veritas.VerifierTraits.fsti.

/// Type definitions
/// ----------------

/// From vcell.h
/// class Addr: an address of a memory
///
/// Note: this is a value which greatly simplifies things in Low*.
type addr = {
  a0:UInt64.t;
  a1:UInt64.t;
  a2:UInt64.t;
  a3:UInt64.t
}

/// From merkle.h
/// Merkle address identifies a location in the sparse merkle tree
type merkle_addr = {
  path: addr;
  depth: UInt16.t
}

/// From merkle_vcell.h
noeq
type merkle_leaf = {
  addr: merkle_addr;   //32 bytes
  data_vcell: B.pointer VCell.t
}

// 32 bytes
let hash_value = UInt128.t & UInt128.t

/// From merkle_vcell.h
///
/// 32; 32; 64; 4; 4 = 136 <= sizeof uint64 * 20
type merkle_internal =
{
   left: hash_value;    // Typically, say, 32 bytes as a pair of UInt128s
   right: hash_value;
   dpath: addr & addr; // Not yet sure exactly what these additional fields represent
   depth: UInt32.t;
   ddepth: UInt16.t & UInt16.t
}

/// CachePolicy, from veritas/common/common.h
type cache_policy =
  | Merkle
  | Blum
  | BlumHash

/// A slot in the cache stores either a leaf or an internal node
noeq
type slot =
  | MerkleLeaf  of merkle_leaf
  | MerkleInternal of merkle_internal


/// An entry is a slot paired with the metadata for use by the cache
noeq
type entry = {
  slot: slot; // this is the field that is an std::array<uint64, 20> in C++
  cp: cache_policy;
  occupied: bool;
  touched: bool;
}

let lbuffer a l =
  b:B.buffer a { B.length b == l }

/// The main type provided by vcache encapsulates a fixed array of
/// cache entries.
///
/// Note that the run-time representation does not depend on t (otherwise, a
/// trick like https://github.com/FStarLang/kremlin/issues/183 would be needed).
///
/// TODO: hide this behind the abstraction once it's ready.
noeq
type t (tr: VerifierTraits.t) = {
  entries: lbuffer entry (UInt16.v tr.VerifierTraits.cache_size)
}

/// Stateful API
/// ------------
///
/// In order to make sure you're not forgetting anything, it's always a good
/// idea to refer to hacl-star/code/streaming/Hacl.Streaming.Interface and make
/// sure you're implementing at least the stateful type class, which is the bare
/// minimum for your clients to be able to do something with your code.

/// We have some abstract invariants on caches, e.g., liveness properties etc.
/// This also includes freeable, which we'll need to implement the free function.
val invariant (#tr: VerifierTraits.t) (h: HS.mem) (cache: t tr): Type0

/// We aim for a static footprint. Note that this is just about the array of
/// entries, knowing that vcells are values means that we don't have to be more
/// complicated than that.
val footprint (#tr: VerifierTraits.t) (cache: t tr): GTot B.loc

val invariant_loc_in_footprint: #tr:VerifierTraits.t -> h:HS.mem -> cache:t tr -> Lemma
    (requires (invariant h cache))
    (ensures (B.loc_in (footprint cache) h))
    [ SMTPat (invariant h cache) ]

/// For spec purposes, a cache is a sequence of entries
val entries (#tr: VerifierTraits.t) (h: HS.mem) (cache: t tr):
  GTot (Seq.lseq entry (UInt16.v (tr.VerifierTraits.cache_size)))

val frame_invariant: #tr:VerifierTraits.t -> l:B.loc -> cache:t tr -> h0:HS.mem -> h1:HS.mem -> Lemma
    (requires (
      invariant h0 cache /\
      B.loc_disjoint l (footprint cache) /\
      B.modifies l h0 h1))
    (ensures (
      invariant h1 cache /\
      entries h0 cache == entries h1 cache /\
      footprint cache == footprint cache))
    [ SMTPat (invariant h1 cache); SMTPat (B.modifies l h0 h1) ]

/// Cache entries are indexed by u16 values
let vcache_idx = UInt16.t

/// The C++ API allows looking up cache entries and returns them by reference.
/// These references are then read and mutated by client code in vmem_vops.h etc.
///
/// We go for something simpler and assume clients of this module will keep
/// track of an index, rather than manipulate raw values (this would greatly
/// complicate the framing lemmas).

/// Note that this returns a value via a dereference.
val get_entry (#tr: VerifierTraits.t) (cache: t tr) (idx: vcache_idx { idx `FStar.UInt16.lt` tr.VerifierTraits.cache_size }):
  Stack entry
    (requires fun h0 ->
      invariant h0 cache)
    (requires fun h0 e h1 ->
      e == Seq.index (entries h0 cache) (UInt16.v idx) /\
      h0 == h1)

val set_entry (#tr: VerifierTraits.t) (cache: t tr)
  (idx: vcache_idx { idx `FStar.UInt16.lt` tr.VerifierTraits.cache_size })
  (entry: entry):
  Stack unit
    (requires fun h0 ->
      invariant h0 cache)
    (requires fun h0 _ h1 ->
      invariant h1 cache /\
      B.modifies (footprint cache) h0 h1 /\
      entries h1 cache == Seq.upd (entries h0 cache) (UInt16.v idx) entry)
