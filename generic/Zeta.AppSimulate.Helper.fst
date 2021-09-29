module Zeta.AppSimulate.Helper

module S = FStar.Seq

let app_state_feq_implies_equal (#adm:_) (st1 st2: app_state adm)
  : Lemma (requires (app_state_feq st1 st2))
          (ensures (st1 == st2))
  = admit()

let of_key (#adm:_) (ki: app_key adm) (r: app_record adm)
  = let k,_ = r in
    k = ki

let refs_comp (#app:_) (fc: appfn_call app) (k: app_key app.adm)
  : b:bool { b <==> refs fc k }
  = let open Zeta.SeqIdx in
    exists_elems_with_prop_comp (of_key k) fc.inp_c

(* for a referenced key, return the parameter position index *)
let refkey_idx (#app:_) (fc: appfn_call app) (k: app_key app.adm{fc `refs` k})
  : i:_{let k',v = FStar.Seq.index fc.inp_c i in k' = k}
  = let open Zeta.SeqIdx in
    last_idx (of_key k) fc.inp_c

let refs_witness (#app:_) (fc: appfn_call app) (k: app_key app.adm)
 (i: Zeta.SeqAux.seq_index fc.inp_c {k = fst (FStar.Seq.index fc.inp_c i)})
  : Lemma (ensures (refs fc k))
 = let open Zeta.SeqIdx in
   exists_elems_with_prop_intro (of_key k) fc.inp_c i

let record_incorrect (#adm:_) (st: app_state adm) (r: app_record adm)
  : bool
  = let k,v = r in
    st k <> v

let input_correct_is_input_consistent (#app:_) (fc: appfn_call app) (st: app_state app.adm)
  : Lemma (ensures (let rs = fc.inp_c in
                   input_consistent fc st <==> input_correct st rs))
  = let rs = fc.inp_c in
    if input_correct st rs then (
      let aux (k:_)
        : Lemma (ensures (fc `refs` k ==> refkey_inp_val fc k = st k))
        = if fc `refs_comp` k then (
            let i = refkey_idx fc k in
            ()
          )
      in
      FStar.Classical.forall_intro aux
    )
    else (
      let open Zeta.SeqIdx in
      let i = last_idx (record_incorrect st) rs in
      let k,v = S.index rs i in
      FStar.Classical.exists_intro (fun i -> (let k',v = S.index fc.inp_c i in k' = k)) i;
      assert(fc `refs` k);
      FStar.Classical.exists_intro (fun k -> (fc `refs` k /\ ~ (refkey_inp_val fc k = st k))) k
    )

let correct_succeeds_if_input_consistent (#app:_) (fc: appfn_call app) (st: app_state app.adm)
  : Lemma (ensures (succeeds fc st <==> correct fc /\ input_consistent fc st))
  = ()

let lemma_post_state (#app:_) (fc: appfn_call app) (st: app_state app.adm {succeeds fc st}) (k: app_key app.adm)
  : Lemma (ensures (let stpost = apply_trans fc st in
                    (* fc references k and the value of k in stpost is the written value *)
                    fc `refs` k /\ write fc k = stpost k
                      \/
                    ~ (fc `refs` k) /\ stpost k = st k))
  = admit()

let prefix_of_valid_valid (#app:_) (fs: seq (appfn_call app) {valid fs}) (i: nat {i <= length fs})
  : Lemma (ensures (valid (prefix fs i)))
  = admit()

let lemma_apply_trans (#app:_) (fs: seq (appfn_call app) {length fs > 0 /\ valid fs})
  : Lemma (ensures (let fs' = hprefix fs in
                    let fc = telem fs in
                    post_state fs == apply_trans fc (post_state fs')))
  = admit()

let lemma_valid_empty (#app:_) (fs: seq (appfn_call app){length fs = 0})
  : Lemma (ensures (valid fs))
  = admit()

let lemma_init_value_null (#app:_) (fs: seq (appfn_call app){length fs = 0}) (k: app_key app.adm)
  : Lemma (ensures (post_state fs k = Null))
  = admit()

let empty_call_result_valid (#app:_) (rs: seq (appfn_call_res app))
  : Lemma (ensures (length rs = 0 ==> valid_call_result rs))
  = admit()

let app_fcs_empty (#app:_) (fcrs: seq (appfn_call_res app))
  : Lemma (ensures (length fcrs = 0 ==> length (app_fcs fcrs) = 0))
   = ()

let app_fcs_snoc (#app:_) (fcrs: seq (appfn_call_res app) {length fcrs > 0})
  : Lemma (ensures (let i = length fcrs - 1 in
                    let fcrs' = prefix fcrs i in
                    let fc = to_app_fc fcrs i in
                    app_fcs fcrs = append1 (app_fcs fcrs') fc))
  = let i = length fcrs - 1 in
    let fcrs' = prefix fcrs i in
    let fcs = app_fcs fcrs in
    let fcs' = app_fcs fcrs' in
    let fc = to_app_fc fcrs i in
    let fcs2 = append1 fcs' fc in
    let aux (i:_)
      : Lemma (ensures (index fcs i = index fcs2 i))
      = ()
    in
    FStar.Classical.forall_intro aux;
    assert(equal fcs fcs2)

let valid_call_result_snoc (#app:_) (fcrs: seq (appfn_call_res app) {length fcrs > 0})
  : Lemma (requires (let i = length fcrs - 1  in
                     let fcrs' = prefix fcrs i in
                     valid_call_result fcrs'))
          (ensures (let i = length fcrs - 1 in
                    let fcrs' = prefix fcrs i in
                    let fcs' = app_fcs fcrs' in
                    let st' = post_state fcs' in
                    let fc = to_app_fc fcrs i in
                    let fcr = index fcrs i in
                    succeeds fc st' ==>
                    fcr.res_cr = result fc ==>
                    valid_call_result fcrs))
  = admit()

let distinct_keys_comp (#app:_) (sk: FStar.Seq.seq (app_record app))
  : b:bool {b <==> distinct_keys sk}
  = admit()
