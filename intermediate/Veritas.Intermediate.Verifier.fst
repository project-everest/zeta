module Veritas.Intermediate.Verifier
open FStar.Integers
open Veritas.Intermediate.Common
module S = Veritas.Intermediate.Store


noeq
type thread_state_t = {
  id           : thread_id_t;
  st           : S.vstore;  //a map from keys (cache ids) to merkle leaf or internal nodes
  clock        : timestamp;
  hadd         : prf_set_hash; //current incremental set hash values; TODO
  hevict       : prf_set_hash;
}
