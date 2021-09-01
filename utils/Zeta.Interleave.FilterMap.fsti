module Zeta.Interleave.FilterMap

open Zeta.Interleave
open Zeta.FilterMap

val ilfilter_map (#a #b:eqtype) (#p:_)
  (fm: ssfm_t a b p)
  (il: interleaving a {Seq.length (s_seq il) = p})
  : il': interleaving b{s_seq il' = ssfilter_map fm (s_seq il)}
