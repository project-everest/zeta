module Zeta.HashFunction

open Zeta.Hash
open Zeta.App
open Zeta.Record
module T = Zeta.Steel.FormatsManual

module ZSH = Zeta.Steel.HashValue
module KU = Zeta.Steel.KeyUtils

let lower_desc_hash (dh:Zeta.Merkle.desc_hash_t)
  : GTot T.descendent_hash
  = let open Zeta.Merkle in
    match dh with
    | Empty -> T.Dh_vnone ()
    | Desc k h b -> 
      let k = KU.lower_base_key k in
      let h = Zeta.Steel.BitUtils.u256_of_bitvec h in
      let b = if b then T.Vtrue else T.Vfalse in
      T.(Dh_vsome ({ dhd_key = k;
                     dhd_h = h;
                     evicted_to_blum = b }))
  
let lower_value (v:value Zeta.Steel.ApplicationTypes.aprm)
  : GTot T.value
  = match v with
    | AppV Null -> T.DValue None
    | AppV (DValue iv) -> T.DValue (Some iv)
    | IntV smv -> T.MValue ({ l = lower_desc_hash smv.left;
                             r = lower_desc_hash smv.right })

let ghashfn (#aprm:app_params) (v:value aprm)
  : GTot hash_value
  = let b = FStar.StrongExcludedMiddle.strong_excluded_middle 
               (aprm == Zeta.Steel.ApplicationTypes.aprm)
    in
    if b 
    then (
      let tv = lower_value v in
      let h = ZSH.hashfn tv in
      Zeta.Steel.BitUtils.bitvec_of_u256 h
    )
    else (
      zero
    )

assume //This assume remains because the generic verifier is in Tot rather than GTot
val hashfn' (#aprm:app_params) (v:value aprm)
  : Tot (h:hash_value { h == ghashfn v })

let hashfn v = hashfn' v

