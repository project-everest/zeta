module Zeta.GenericVerifier

let get_record_set (#vspec: verifier_spec_base) (ss: S.seq (vspec.slot_t)) (vtls: vspec.vtls_t {vspec.valid vtls}):
  (let record_t = app_record vspec.app.adm in
   ors: option (S.seq record_t) {Some? ors ==> (let rs = Some?.v ors in
                                                S.length rs = S.length ss /\
                                                SA.distinct_elems ss /\
                                                distinct_keys #vspec.app.adm rs)})
  = admit()

let get_record_set_correct
  (#vspec: _)
  (ss: S.seq (vspec.slot_t))
  (vtls: vspec.vtls_t {vspec.valid vtls})
  (i: SA.seq_index ss)
  : Lemma (requires (Some? (get_record_set ss vtls)))
          (ensures (let rs = get_record_set_succ ss vtls in
                    let s = S.index ss i in
                    let ak,av = S.index rs i in
                    Some? (vspec.get s vtls) /\
                    (let gk,gv = Some?.v (vspec.get s vtls) in
                     let open Zeta.GenKey in
                     gk = AppK ak /\
                     gv = AppV av)))
  = admit()


let update_record_set (#vspec: verifier_spec_base)
                      (ss: S.seq (vspec.slot_t))
                      (vtls: vspec.vtls_t {vspec.valid vtls /\ Some? (get_record_set ss vtls)})
                      (ws: S.seq (app_value_nullable vspec.app.adm) {let rs = get_record_set_succ ss vtls in
                                                                     S.length ws = S.length rs})
  : vtls':vspec.vtls_t{vspec.valid vtls'}
  = admit()

let update_record_set_valid
  (#vspec: _)
  (ss: S.seq (vspec.slot_t))
  (vtls: vspec.vtls_t {vspec.valid vtls /\ Some? (get_record_set ss vtls)})
  (ws: S.seq (app_value_nullable vspec.app.adm) {let rs = get_record_set_succ ss vtls in
                                                 S.length ws = S.length rs})
  (i: SA.seq_index ss)
  : Lemma (ensures (let rs = get_record_set_succ ss vtls in
                    let vtls' = update_record_set ss vtls ws in
                    let s = S.index ss i in
                    let ak,_ = S.index rs i in
                    Some? (vspec.get s vtls') /\
                    (let gk,gv = Some?.v (vspec.get s vtls') in
                     let open Zeta.GenKey in
                     gk = AppK ak /\
                     gv = AppV (S.index ws i))))
  = admit()

let runapp_doesnot_change_nonref_slots
  (#vspec: verifier_spec)
  (e: verifier_log_entry vspec {is_appfn e})
  (vs: vspec.vtls_t)
  (s: vspec.slot_t)
  : Lemma (requires (let RunApp _ _ ss = e in
                     vspec.valid (verify_step e vs) /\ not (S.mem s ss)))
          (ensures (let vs' = verify_step e vs in
                    vspec.get s vs == vspec.get s vs'))
  = admit()

let runapp_doesnot_change_slot_emptiness
  (#vspec: verifier_spec)
  (e: verifier_log_entry vspec {is_appfn e})
  (vs: vspec.vtls_t)
  (s: vspec.slot_t)
  : Lemma (requires (let RunApp _ _ ss = e in
                     vspec.valid (verify_step e vs)))
          (ensures (let vs' = verify_step e vs in
                    (None = vspec.get s vs) <==> (None = vspec.get s vs')))
  = admit()
