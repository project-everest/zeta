module VCache

/// We started trying to model some of the key data structures and
/// APIs reachable from vcache.h.
///
/// Here's some F* pseudocode sketching our understanding so far, with
/// several questions along the way.


/// Most of the code is templatized in C++ by verifier traits. We can
/// model that in F* as a typeclass. We're gathering elements of this
/// typeclass as we go
class verifier_traits (t:Type) = {
  vcell:Type;    //The type of vcell, e.g, a pair of UInt64s
  cacheSize: u:nat { u < 0xffff }; //the size of the cache, bounded by the size of VCacheIdx
  hasher:_;      //TBD: also a typeclass of its own, eventually instantiated with something from EverCrypt
  hashValue:_;   //TBD: dependent on the hasher typeclass, e.g., a pair of UInt128
}


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
type merkle_leaf (v:Type) [| verifier_traits v ] = {
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

/// A ghost deref of an entry_ref, for spec
val entry_ref_value (e:entry_ref cache)  (m:mem{cache_invariant cache mem}) : GTot entry

/// The underlying index of an entry, ghostly
val idx_of_entry (e:entry_ref cache) : GTot vcache_idx

/// We could then provide an API to gen an entry
val get_entry (v:Type) [| verifier_traits v |] (cache:t v) (idx:vcache_idx {idx < cacheSize})
  : ST entry_ref
       (requires fun m0 -> cache_invariant cache m0)
       (requires fun m0 e m1 ->
         cache_invariant cache m1 /\
         e == Seq.index (entries cache m1) idx /\
         modifies loc_none m0 m1)

/// Mutating an entry
val set_data (#cache: _) (e:entry_ref cache) (v:slot)
  : ST unit
       (requires fun m0 -> cache_invariant cache m0)
       (requires fun m0 e m1 ->
         cache_invariant cache m1 /\
         e == Seq.update (entries cache m1) (idx_of_entry e) ({ entry_ref_value e m0 with slot=v}) /\
         modifies (loc_entry e) m0 m1)

/// Reading an entry
val get_data (#cache:_) (e:entry_ref cache)
  : ST slot
       (requires fun m0 -> cache_invariant cache m0)
       (ensures fun m0 s m1 ->
         cache_invariant cache m1 /\
         modifies loc_none m0 m1 /\
         s == (entry_ref_value e m1).slot)
