module Zeta.Steel.AEADHandle
module G = Zeta.Steel.Globals
module AEAD = EverCrypt.AEAD
module NullableRef = Steel.Reference
open Steel.ST.Util

val get_aead_state (_:unit)
  : STT (NullableRef.ref AEAD.state_s)
        emp
        (fun p -> AEAD.state_inv p G.aead_key)
