module Zeta.EAC

open Zeta.SeqAux

let eac_implies_prefix_eac
  (#app: app_params)
  (l: eac_log app)
  (i: nat {i <= length l})
  : Lemma (ensures (eac (prefix l i)))
  =

  admit()

let max_eac_prefix
  (#app: app_params)
  (l:vlog_ext app)
  : (i:nat{eac l /\ i = length l
          \/
          i < length l /\
          eac (prefix l i) /\
          ~ (eac (prefix l (i + 1)))})
  = admit()

(* computable version of eac *)
let is_eac_log (#app: app_params) (l:vlog_ext app): (r:bool{r <==> eac l})
  = let i = max_eac_prefix l in
    if i = length l
    then true
    else false
