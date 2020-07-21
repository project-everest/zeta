module VerifierTraits


/// Most of the code is templatized in C++ by verifier traits. We can
/// model that in F* as a typeclass. We're gathering elements of this
/// typeclass as we go
class verifier_traits (t:Type) = {
  vcell:Type;    //The type of vcell, e.g, a pair of UInt64s
  cacheSize: u:nat { u < 0xffff }; //the size of the cache, bounded by the size of VCacheIdx
  hasher:_;      //TBD: also a typeclass of its own, eventually instantiated with something from EverCrypt
  hashValue:_;   //TBD: dependent on the hasher typeclass, e.g., a pair of UInt128
  maxVOpSize : uint_32
}
