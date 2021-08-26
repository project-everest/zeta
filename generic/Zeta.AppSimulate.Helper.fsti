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

(* equality of two app states *)
let app_state_feq #adm (st1 st2: app_state adm)
  = forall (k: app_key adm). {:pattern (st1 k = st2 k)} st1 k = st2 k

val app_state_feq_implies_equal (#adm:_) (st1 st2: app_state adm)
  : Lemma (requires (app_state_feq st1 st2))
          (ensures (st1 == st2))
          [SMTPat (app_state_feq st1 st2)]

(* a correct function call is one which does not fail on the input *)
let correct #app (fc: appfn_call app)
  = let fn = appfn fc.fid_c in
    let rc,_,_ = fn fc.arg_c fc.inp_c in
    rc = Fn_success

let result #app (fc: appfn_call app{correct fc})
  = let fn = appfn fc.fid_c in
    let _,res,_ = fn fc.arg_c fc.inp_c in
    res

let writes #app (fc: appfn_call app{correct fc})
  = let fn = appfn fc.fid_c in
    let _,_,ws = fn fc.arg_c fc.inp_c in
    ws

(* does a function call reference a specific app key *)
let refs #app (fc: appfn_call app) (k: app_key app.adm)
  = let open FStar.Seq in
  exists i. (let k',v = index fc.inp_c i in k = k')

(* for a referenced key, return the parameter position index *)
val refkey_idx (#app:_) (fc: appfn_call app) (k: app_key app.adm{fc `refs` k})
  : i:_{let k',v = FStar.Seq.index fc.inp_c i in k' = k}

(* the written-value of a key *)
let write #app (fc: appfn_call app{correct fc}) (k: app_key app.adm{fc `refs` k})
  = let i = refkey_idx fc k in
    let ws = writes fc in
    let open FStar.Seq in
    index ws i



(* does a fncall succeed for a given state and input? *)
let succeeds #app (fc: appfn_call app)
  = Some? (simulate_step fc st)

(* for a successful proc call, the state after applying the function *)
let apply #app (fc: appfn_call app) (st: app_state app.adm {succeeds fc st})
  = let Some (st, _) = simulate_step fc st in
    st

(* for a referenced key, the input value provided to the function invocation *)
let refkey_inp_val (#app:_) (fc: appfn_call app) (k: app_key app.adm{fc `refs` k})
  = let open FStar.Seq in
    let i = refkey_idx fc k in
    let _,v = index fc.inp_c i in
    v

(* if a function application succeeds, then the input value provided as input for a key is consistent
 * with the "pre" state *)
val lemma_refkey_pre_val (#app:_)
  (fc: appfn_call app)
  (st: app_state app.adm)
  (k: app_key app.adm{fc `refs` k})
  : Lemma (requires (succeeds fc st))
          (ensures (refkey_inp_val fc k = st k))

let refkey_post_val #app (fc: appfn_call app) (k: _{fc `refs` k})
  = let fn = appfn fc.fid_c in
    let rc
