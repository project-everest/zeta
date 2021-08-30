module Zeta.AppSimulate.Helper

open Zeta.App
open Zeta.AppSimulate

(* Helper lemmas for reasoning about app simulate *)

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

val refs_comp (#app:_) (fc: appfn_call app) (k: app_key app.adm)
  : b:bool { b <==> refs fc k }

(* for a referenced key, return the parameter position index *)
val refkey_idx (#app:_) (fc: appfn_call app) (k: app_key app.adm{fc `refs` k})
  : i:_{let k',v = FStar.Seq.index fc.inp_c i in k' = k}

val refs_witness (#app:_) (fc: appfn_call app) (k: app_key app.adm)
 (i: Zeta.SeqAux.seq_index fc.inp_c {k = fst (FStar.Seq.index fc.inp_c i)})
  : Lemma (ensures (refs fc k))

(* for a referenced key, the input value provided to the function invocation *)
let refkey_inp_val (#app:_) (fc: appfn_call app) (k: app_key app.adm{fc `refs` k})
  = let open FStar.Seq in
    let i = refkey_idx fc k in
    let _,v = index fc.inp_c i in
    v

(* the written-value of a key *)
let write #app (fc: appfn_call app{correct fc}) (k: app_key app.adm{fc `refs` k})
  = let i = refkey_idx fc k in
    let ws = writes fc in
    let open FStar.Seq in
    index ws i

(* does a fncall succeed for a given state and input? *)
let succeeds #app (fc: appfn_call app) (st: app_state app.adm)
  = Some? (simulate_step fc st)

(* the inputs of a function call are consistent with a state, if the values of all referenced keys are those
 * in the state *)
let input_consistent #app (fc: appfn_call app) (st: app_state app.adm)
  = forall (k: app_key app.adm). {:pattern (refkey_inp_val fc k = st k)} fc `refs` k ==> (refkey_inp_val fc k = st k)

val input_correct_is_input_consistent (#app:_) (fc: appfn_call app) (st: app_state app.adm)
  : Lemma (ensures (let rs = fc.inp_c in
                   input_consistent fc st <==> input_correct st rs))
          [SMTPat (input_consistent fc st)]

(* a state transition is guaranteed to succeed on a correct function call if the inputs are consistent
 * with the state *)
val correct_succeeds_if_input_consistent (#app:_) (fc: appfn_call app) (st: app_state app.adm)
  : Lemma (ensures (succeeds fc st <==> correct fc /\ input_consistent fc st))

(* for a successful proc call, the state after applying the function *)
let apply_trans #app (fc: appfn_call app) (st: app_state app.adm {succeeds fc st})
  = let Some (st, _) = simulate_step fc st in
    st

(* in the post state of applying a transition function, the value of an unreferenced key is the same;
 * the value of a referenced key is that produced by the write of the function *)
val lemma_post_state (#app:_) (fc: appfn_call app) (st: app_state app.adm {succeeds fc st}) (k: app_key app.adm)
  : Lemma (ensures (let stpost = apply_trans fc st in
                    (* fc references k and the value of k in stpost is the written value *)
                    fc `refs` k /\ write fc k = stpost k
                      \/
                    ~ (fc `refs` k) /\ stpost k = st k))

open FStar.Seq
open Zeta.SeqAux

(* a valid sequence is a sequence that does not fail *)
let valid (#app:_) (fs: seq (appfn_call app))
  = Some? (simulate fs)

let post_state #app (fs: seq (appfn_call app) {valid fs})
  = let Some (st,_) = simulate fs in
    st

val prefix_of_valid_valid (#app:_) (fs: seq (appfn_call app) {valid fs}) (i: nat {i <= length fs})
  : Lemma (ensures (valid (prefix fs i)))
          [SMTPat (prefix fs i)]

val lemma_apply_trans (#app:_) (fs: seq (appfn_call app) {length fs > 0 /\ valid fs})
  : Lemma (ensures (let fs' = hprefix fs in
                    let fc = telem fs in
                    post_state fs == apply_trans fc (post_state fs')))
          [SMTPat (valid fs)]

val lemma_valid_empty (#app:_) (fs: seq (appfn_call app){length fs = 0})
  : Lemma (ensures (valid fs))

val lemma_init_value_null (#app:_) (fs: seq (appfn_call app){length fs = 0}) (k: app_key app.adm)
  : Lemma (ensures (post_state fs k = Null))
