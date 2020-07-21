module Veritas.VCache

open VerifierTraits

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
  a0:uint_64;
  a1:uint_64;
  a2:uint_64;
  a3:uint_64
}

/// From merkle.h
/// Merkle address identifies a location in the sparse merkle tree
type merkle_addr = {
  path: addr;
  depth: uint_16
}

/// From merkle_vcell.h
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
   depth: uint32;
   ddepth: uint16 & uint16
}

/// From vcache.h
/// CachePolicy is an enum in C++. We encode it ...
///
/// JP: we voted against ``type cache_policy = Merkle | Blum | BlumHash``. Why?
/// (The constants would be 1, 2, 3 instead of 1, 2, 4 but not a big deal?). It
/// would also give use pattern-matches.
let merkle = 0x01ul
let blum = 0x02ul
let blum_hash = 0x04ul
let cache_policy = u:uint8_t{ u = 0x01 \/ u = 0x02 \/ u=0x04 }

/// A slot in the cache stores either a leaf or an internal node
type slot =
  | MerkleLeaf  of merkle_leaf
  | MerkleInternal of merkle_internal


/// An entry is a slot paired with the metadata for use by the cache
type entry = {
  slot: slot; // this is the field that is an std::array<uint64, 20> in C++
  cp: cache_policy;
  occupied: bool;
  touched: bool;
}

/// The main type provided by vcache encapsulates a fixed array of
/// cache entries.
///
type t (tr: VerifierTraits.t) = {
  entries:Buffer.lbuffer entry (UInt32.v tr.cache_size)
}

/// Stateful API
/// ------------

/// We have some abstract invariants on caches, e.g., liveness properties etc.
val cache_invariant (#v:Type) [| verifier_traits v |] (c: t v) : mem -> prop

/// We have to aim for a static footprint. Note that this is just about the
/// array of entries, not the vcells pointed to by the entries themselves (to be
/// discussed).
val footprint: #v:Type -> [| verified_traits v |] -> t v -> B.loc

val frame_invariant: #v:Type -> [| verified_traits v |] -> l:B.loc -> h0:HS.mem -> h1:HS.mem -> c:t v -> Lemma
  (requires (
    B.modifies l h0 h1 /\
    B.loc_disjoint l (footprint c) /\
    cache_invariant c h0))
  (ensures (
    cache_invariant c h1))

/// For spec purposes, a cache is a sequence of entries
val entries (#v:_) [|verifier_traits v] (c:t v) (m:mem{cache_invariant c m})
  : GTot (seq entry)

/// Cache entries are indexed by u16 values
let vcache_idx = uint_16

/// The C++ API allows looking up cache entries and returns them by reference.
/// These references are the read and mutated by client code in vmem_vops.h etc.
///
/// To model this, we define an abstract type of references to cache entries
/// The type is indexed by the cache in which the entries reside
val entry_ref (cache: t v) : Type
(* Internally, entry_ref can be implemented as a pointer to a entry,
    together with some specificational data, e.g., the indexed in the
    cache to which it points. The liveness of an entry_ref is
    determined by the liveness of the cache itself--so long as cache
    is live, then all its entry_refs are usable *)

/// A ghost deref of an entry_ref, for spec. TODO: consistent naming, e.g. entry_v?
val entry_ref_value #cache(e:entry_ref cache)  (m:mem{cache_invariant cache mem}) : GTot entry

/// The underlying index of an entry, ghostly
val idx_of_entry (e:entry_ref cache) : GTot vcache_idx

/// A lemma that ties together idx_of_entry, entry_ref_value and entries. Note
/// that we have a mix of styles: the relationship between cache and e is
/// expressed via an index, while the relationship between e and index is
/// expressed via a predicate. TODO: figure out if there's a need to change this.
val entry_ref_is_seq_index #cache (e: entry_ref cache) h idx: Lemma
  (requires (idx_of_entry e == idx))
  (ensures (
    entry_ref_value e h == Seq.index (entries h cache) idx))

/// We could then provide an API to gen an entry. JP: using m0 == m1 (no need to
/// frame the invariant, no need to perform modifies-reasoning).
val get_entry (v:Type) [| verifier_traits v |] (cache:t v) (idx:vcache_idx {idx < cacheSize})
  : ST (entry_ref cache)
       (requires fun m0 -> cache_invariant cache m0)
       (requires fun m0 e m1 ->
         idx_of_entry e == idx /\
         m0 == m1)
