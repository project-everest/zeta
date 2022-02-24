module Zeta.Steel.EpochHashes
open Steel.ST.Util
open Zeta.Steel.Util
module M = Zeta.Steel.ThreadStateModel
module HA = Zeta.Steel.HashAccumulator


[@@CAbstractStruct]
noeq
type epoch_hashes_t = {
  hadd: HA.ha;
  hevict: HA.ha;
}

let epoch_hash_perm (k:M.epoch_id)
                    (v:epoch_hashes_t)
                    (c:M.epoch_hash) =
    HA.ha_val v.hadd c.hadd `star`
    HA.ha_val v.hevict c.hevict
