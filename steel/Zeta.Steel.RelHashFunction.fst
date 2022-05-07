module Zeta.Steel.RelHashFunction
friend Zeta.HashFunction
open Zeta.Steel.Rel

open Zeta.Hash
open Zeta.App
open Zeta.Record
module T = Zeta.Steel.FormatsManual

module ZSH = Zeta.Steel.HashValue
module KU = Zeta.Steel.KeyUtils
module ZH = Zeta.HashFunction

let related_desc_hash_inv (sdh:T.descendent_hash)
                          (idh:Zeta.Merkle.desc_hash_t)
  : Lemma 
    (requires related_desc_hash sdh idh)
    (ensures ZH.lower_desc_hash idh == sdh)
  = match sdh, idh with
    | T.Dh_vnone _, _ -> ()
    | T.Dh_vsome sdh, Zeta.Merkle.Desc k h b ->
      BitUtils.inverse h
  
let related_val_inv (sv:s_val) (iv:i_val)
  : Lemma 
    (requires related_val sv iv)
    (ensures ZH.lower_value iv == sv)
  = match sv, iv with
    | T.DValue None, _ -> ()
    | T.DValue (Some sdv), _ -> ()
    | T.MValue mv, IntV smv ->
      related_desc_hash_inv mv.l smv.left;
      related_desc_hash_inv mv.r smv.right

(* the hash of two related values is related *)
let related_hashfn (sv: s_val) (iv: i_val)
  : Lemma (requires (related_val sv iv))
          (ensures (related_hash_value (s_hashfn sv) (i_hashfn iv)))
  = assert (ZH.hashfn iv ==
           Zeta.Steel.BitUtils.bitvec_of_u256 (s_hashfn (ZH.lower_value iv)));
    related_val_inv sv iv
