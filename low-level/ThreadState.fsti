module ThreadState
open VerifierTraits
module VCache = VCache

let vopBuf (v:Type) [| verifier_traits v |] =
  lbuffer uint64_t (maxVOpSize / 8)

type thread_state (v:Type) [| verifier_traits v |] = {

       // Id of this thread
  threadId id;

        // Current epoch
  epochId curEpoch;

        // Counter within current epoch
  counter clock;

        // Psuedo-random function to compute the set hashes
        PRF prf;

  // hrs \xor hws of previous epoch
  PRFSetHash hPrevEpoch;

  // hrs \xor hws of current epoch
        PRFSetHash hCurEpoch;

        // Has previous epoch been verified
        bool prevEpochVerified;

        // verifier cache
  cache : VCache.t v;

        // Buffer to construct vops
  vopBuf : vOpBuf v;

        // Cryptographic hash computer
  hasher : hasher;
}
