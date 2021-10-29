module Zeta.AppSimulate

let prefix_of_distinct_distinct
  (#adm: app_data_model)
  (sk: S.seq (app_record adm) {distinct_keys #adm sk})
  (i: nat { i <= S.length sk }) :
  Lemma (ensures (let sk' = SA.prefix sk i in
                  distinct_keys #adm sk'))
  = ()

let of_key (#adm:_) (ki: app_key adm) (r: app_record adm)
  = let k,_ = r in
    k = ki

let input_incorrect_idx (#adm:_) (st: app_state adm) (r: app_record adm)
  : bool
  = let k,v = r in
    st k <> v

let input_correct (#adm: app_data_model)
  (st: app_state adm)
  (inp: S.seq (app_record adm))
  : Tot (b: bool{b <==>
                (forall (i: SA.seq_index inp).
                    let k,v = S.index inp i in
                    st k = v)})
  = let open Zeta.SeqIdx in
    not (exists_elems_with_prop_comp (input_incorrect_idx st) inp)

let refs_comp (#app:_) (fc: appfn_call app) (k: app_key app.adm)
  : b:bool { b <==> refs fc k }
  = let open Zeta.SeqIdx in
    exists_elems_with_prop_comp (of_key k) fc.inp_c

(* for a referenced key, return the parameter position index *)
let refkey_idx (#app:_) (fc: appfn_call app) (k: app_key app.adm{fc `refs` k})
  : i:_{let k',v = FStar.Seq.index fc.inp_c i in k' = k}
  = let open Zeta.SeqIdx in
    last_idx (of_key k) fc.inp_c
