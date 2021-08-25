module Zeta.AppSimulate

open Zeta.App

module I = Zeta.Interleave
module S = FStar.Seq
module SA = Zeta.SeqAux

(* An invocation of an application function *)
type appfn_call (aprm: app_params) = {

  (* id of the function *)
  fid_c: appfn_id aprm;

  (* arguments of the function *)
  arg_c: appfn_arg fid_c;

  (* the read records of the function call *)
  inp_c: appfn_rs_t fid_c;
}

(* a function call and a result *)
type appfn_call_res (aprm: app_params) = {

  (* id of the function *)
  fid_cr: appfn_id aprm;

  (* arguments of the function *)
  arg_cr: appfn_arg fid_cr;

  (* the read records of the function call *)
  inp_cr: appfn_rs_t fid_cr;

  (* the result of the call *)
  res_cr: appfn_res fid_cr;
}

(* drop the result from a function call result *)
let to_appfn_call #aprm (r: appfn_call_res aprm) =
  {fid_c = r.fid_cr; arg_c = r.arg_cr; inp_c = r.inp_cr }

(* the (full) application state  *)
let app_state (adm: app_data_model) = (k: app_key adm) -> app_value_nullable adm

(* update the value for a record *)
let update #adm (st: app_state adm) (k: app_key adm) (v: app_value_nullable adm): app_state adm =
  fun k' -> if k' = k then v
          else st k'

(* if a sequence has distinct keys, then a prefix of the sequence also has this property *)
val prefix_of_distinct_distinct
  (#adm: app_data_model)
  (sk: S.seq (app_record adm) {distinct_keys #adm sk})
  (i: nat { i <= S.length sk }) :
  Lemma (ensures (let sk' = SA.prefix sk i in
                  distinct_keys #adm sk'))
        [SMTPat (SA.prefix sk i)]

(* check that each record in a sequence of records is consistent with an input state *)
val input_correct (#adm: app_data_model)
  (st: app_state adm)
  (inp: S.seq (app_record adm))
  : Tot (b: bool{b <==>
                (forall (i: SA.seq_index inp).
                    let k,v = S.index inp i in
                    st k = v)})

(* update the state with new values for a sequence of keys (specified as a record) *)
let rec update_seq #adm
  (st: app_state adm)
  (inp: S.seq (app_record adm) {distinct_keys #adm inp})
  (ws: S.seq (app_value_nullable adm) {S.length ws = S.length inp})
  : Tot (app_state adm)
  (decreases (S.length inp)) =

  let n = S.length inp in
  if n = 0 then st
  else
    let inp' = SA.prefix inp (n - 1) in
    let ws' = SA.prefix ws (n - 1) in
    let st = update_seq st inp' ws' in
    let k,_ = S.index inp (n - 1) in
    let v = S.index ws (n - 1) in
    update st k v

(* simulate a single step of an app state transition. return None on failure *)
let simulate_step #aprm (fncall: appfn_call aprm) (st: app_state aprm.adm):
  option ( app_state aprm.adm & appfn_res fncall.fid_c) =
  let fn = appfn fncall.fid_c in
  let rc,res,ws = fn fncall.arg_c fncall.inp_c in
  (* if the input records are not consistent with the state then fail *)
  if not (input_correct st fncall.inp_c) then None
  (* if the function evaluation fails, fail the step *)
  else if rc = Fn_failure then None
  (* No failures: update the state *)
  else Some (update_seq st fncall.inp_c ws, res)

(* initial state of the application *)
let init_app_state (adm: app_data_model): app_state adm =
  fun _ -> Null

(* simulation of app transitions on a function call sequence using the entire app-state *)
let rec simulate #aprm (fs: S.seq (appfn_call aprm)):
  Tot (option (app_state aprm.adm & S.seq (appfn_call_res aprm)))
  (decreases (S.length fs)) =
  let n = S.length fs in
  if n = 0 then
    Some (init_app_state aprm.adm, S.empty #(appfn_call_res aprm))
  else
    let fs' = SA.prefix fs (n-1) in
    let ors = simulate fs' in
    if None? ors then None
    else
      let Some (st', rs') = ors in
      let c = S.index fs (n-1) in
      let or = simulate_step c st' in
      if None? or then None
      else (
        let Some (st, r) = or in
        let r = {fid_cr = c.fid_c; arg_cr = c.arg_c; inp_cr = c.inp_c; res_cr = r} in
        let rs = SA.append1 rs' r in
        SA.lemma_hprefix_append_telem fs;
        Some (st, rs)
      )

(* a function-call-result sequence is valid if we get the result when run simulation on the call parameters *)
let valid #aprm (rs: S.seq (appfn_call_res aprm)) =
  let fs = SA.map to_appfn_call rs in
  Some? (simulate fs) /\
    (let Some (_,rs2) = simulate fs in
     rs2 = rs)

(* a sequence of sequence of function-call-result is sequentially consistent if there exists an
 * interleaving that is valid per the definition above
 *)
let seq_consistent #aprm (sr: S.seq (S.seq (appfn_call_res aprm))) =
  exists is. I.interleave #(appfn_call_res aprm) is sr /\ valid is
