module Zeta.AppSimulate

open Zeta.App

module S = FStar.Seq
module SA = Zeta.SeqAux

(* An invocation of an application function *)
type appfn_call (aprm: app_params) = {

  (* id of the function *)
  fid_call: appfn_id aprm;

  (* arguments of the function *)
  arg: appfn_arg fid_call;

  (* the read records of the function call *)
  inp: appfn_rs_t fid_call;
}

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
  option ( app_state aprm.adm & appfn_res fncall.fid_call) =
  let fn = appfn fncall.fid_call in
  let rc,res,ws = fn fncall.arg fncall.inp in
  if rc = Fn_failure then None
  else Some (update_seq st fncall.inp ws, res)

(* the result of a function. We need this type since the we cannot simply define a
 * seq (result), since the result type depends on the function id.
 *)
type appfn_call_res (aprm: app_params) =
  | FnRes: fid_res: appfn_id aprm -> res: appfn_res fid_res -> appfn_call_res aprm

(* initial state of the application *)
let init_app_state (adm: app_data_model): app_state adm =
  fun _ -> Null

let consistent #aprm (call_seq: S.seq (appfn_call aprm)) (res_seq: S.seq (appfn_call_res aprm)) =
  S.length call_seq = S.length res_seq /\
  (forall (i: SA.seq_index call_seq).
    {:pattern ((S.index call_seq i).fid_call = (S.index res_seq i).fid_res)}
    (S.index call_seq i).fid_call = (S.index res_seq i).fid_res)

let rec simulate #aprm (fs: S.seq (appfn_call aprm)):
  Tot (or: option (app_state aprm.adm & S.seq (appfn_call_res aprm))
        {Some? or ==> (let _,rs = Some?.v or in
                       consistent fs rs)})
  (decreases (S.length fs)) =
  let n = S.length fs in

  admit()
