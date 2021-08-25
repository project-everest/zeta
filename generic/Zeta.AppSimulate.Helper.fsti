module Zeta.AppSimulate.Helper

open Zeta.App
open Zeta.AppSimulate
(* Helper lemmas for reasoning about app simulate *)

(* running a function with arity 0 leaves the state unchanged since the function does not
 * read/write from/to the state *)
val simulate_arity0_leaves_state_unchanged
  (#aprm: app_params)
  (fncall: appfn_call aprm)
  (st: app_state aprm.adm)
  (k: app_key aprm.adm)
  : Lemma (requires (let fid = fncall.fid_c in
                     appfn_arity fid = 0))
          (ensures (let o = simulate_step fncall st in
                    Some? o ==>
                    (let st',_ = Some?.v o in
                     st k = st' k)))
