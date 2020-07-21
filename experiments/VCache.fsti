module VCache
open VerifierTraits

/// We started trying to model some of the key data structures and
/// APIs reachable from vcache.h.
///
/// Here's some F* pseudocode sketching our understanding so far, with
/// several questions along the way.



/// From vcell.h
/// class Addr: an address of a memory
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
type merkle_leaf (v:Type) [| verifier_traits v |] = {
  addr: merkle_addr;   //32 bytes
  data_vcell: B.pointer vcell
}

let hashValue = UInt128.t * UInt128.t

/// From merkle_vcell.h
type merkle_internal (v:Type) [| verifier_traits v |] = //64 bytes * 2; 4; 4 {
   left: hashValue;    // Typically, say, 32 bytes as a pair of UInt128s
   right: hashValue;
   dpath: addr * addr; // Not yet sure exactly what these additional fields represent
   depth: uint32;
   ddepth: uint16 * uint16
}


/// From vcache.h
/// CachePolicy is an enum in C++. We encode it ...
let merkle = 0x01
let blum = 0x02
let blumHash = 0x04
let cache_policy = u:uint8_t{ u = 0x01 \/ u = 0x02 \/ u=0x04 }

/// A slot in the cache stores either a leaf or an internal node
type slot (v:Type) [| verifier_traits v |] =
  | MerkleLeaf  of merkle_leaf v
  | MerkleInternal of merkle_internal v //

/// An entry is a slot paired with the metadata for use by the cache
type entry (v:Type) [| verifier_traits v |] = {
  slot: slot v;
  cp:cache_policy;
  occupied:bool;
  touched:bool;
}

/// The main type provided by vcache encapsulates a fixed array of
/// cache entries.
///
type t (v:Type) [| verifier_traits v |] = {
  entries:Buffer.lbuffer (entry v) cacheSize
}

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

/// Mutating an entry
val set_data (#cache: _) (e:entry_ref cache) (v:slot)
  : ST unit
       (requires fun m0 -> cache_invariant cache m0)
       (requires fun m0 e m1 ->
         cache_invariant cache m1 /\
         entries m1 e == Seq.update (entries cache m1) (idx_of_entry e) ({ entry_ref_value e m0 with slot=v}) /\
         modifies (footprint cache) m0 m1)

/// Reading an entry. Need to understand whether the client will want to modify
/// the data, or if this is read-only. We probably need to encapsulate the slot
/// of each entry in a region, at the very least. We could probably provide a
/// lemma of the form "if client modifies loc_buffer (not loc_addr_of_buffer!)
/// of a slot then the update can be reflected on `entries` and the invariant is
/// preserved".
val get_data (#cache:_) (e:entry_ref cache)
  : ST slot
       (requires fun m0 -> cache_invariant cache m0)
       (ensures fun m0 s m1 ->
         m0 == m1 /\
         s == (entry_ref_value e m1).slot)
