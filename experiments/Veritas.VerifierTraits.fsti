module Veritas.VerifierTraits

/// Note: in the C++ code, VerifierTr ("Verifier Traits") contains a HashTraits
/// (see veritas/crypto/include/crypt_hash.h). Multiple instances of HashTraits
/// (e.g. SHA256Traits) exist. Each HashTrait defines a type, a length of
/// computed hashes, a set of functions to actually compute hashes (Hasher).
/// This is basically a way to do open polymorphism with a finite set of
/// instances. We could do something similar with type classes, but let's rely
/// on agility instead. By using the ``hash_alg`` type, we rely on the agile
/// hash infrastructure from EverCrypt. (We could either have a type class, but
/// that's a little fancy and probably overkill. We could also keep pointers to
/// hash functions at run-time, but this requires more expertise. Maybe later.)

inline_for_extraction noextract
let vcache_idx_max = 0xffff

type verification_scheme =
  | Blum
  | BlumNC
  | Merkle

/// Most of the code is templatized in C++ by verifier traits. We can model that
/// in F*. We're gathering elements of this "verifier_traits" type as we go.
///
/// JP: there are actually multiple instances of VerifierTr (see struct
/// VeritasTrBuilder in veritas/utils/utils.h) which, this being a template,
/// generate a compile-time specialization of the entire call-graph on this.
///
/// We parameterize all of our Low* functions by a verifier_traits (this is our
/// index). Then, we need to settle on a meta-programming technique to generate
/// a decent call-graph if we don't want to inline_for_extraction everything to
/// get the benefits of specialization. This has all been studied in HACL* so we
/// know how to do this.
///
/// Note: if we want this to extract in Low*, let's make sure that #t is always
/// the first argument to our functions, to get ML polymorphism at
/// extraction-time followed by KreMLin's whole-program monomorphization.
type t = {
  cache_size: (cache_size: UInt32.t { UInt32.v cache_size <= vcache_idx_max });
    // JP: picking UInt32t.t here because this will be used at runtime for dynamic memory allocation
    // See common/common.h: using VCacheIdx = uint16_t;
  hash_alg: Spec.Agile.Hash.hash_alg;
    // JP: this should actually be a hash_impl; TODO fixme once Son lands his patch in HACL
    // JP: not all hash algorithms are valid, see remark in Veritas.VCell.fsti
  verification_scheme: verification_scheme;
}
