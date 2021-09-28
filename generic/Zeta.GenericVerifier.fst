module Zeta.GenericVerifier

let is_of_key (#adm) (ak: app_key adm) (r: app_record adm)
  = fst r = ak

open Zeta.SeqIdx

let contains_key (#adm) (ak: app_key adm) (rs: S.seq (app_record adm))
  = exists_elems_with_prop (is_of_key ak) rs

let contains_key_comp (#adm) (ak: app_key adm) (rs: S.seq (app_record adm))
  = exists_elems_with_prop_comp (is_of_key ak) rs

let distinct_keys_snoc (#adm) (rs: S.seq (app_record adm)) (r: app_record adm)
  : Lemma (ensures (let ak, av = r in
                    distinct_keys rs ==>
                    ~ (contains_key ak rs) ==>
                    distinct_keys (SA.append1 rs r)))
          [SMTPat (SA.append1 rs r)]
  = admit()

let contains_app_key_base (#vspec: verifier_spec_base)
  (vtls: vspec.vtls_t{ vspec.valid vtls })
  (ss: S.seq (vspec.slot_t)) (i: SA.seq_index ss)
  = let s = S.index ss i in
    Some? (vspec.get s vtls) &&
    (let gk,gv = Some?.v (vspec.get s vtls) in
     Zeta.GenKey.AppK? gk)

module IF = Zeta.IdxFnInt

let gen_seq (#vspec: verifier_spec_base) (vtls: vspec.vtls_t {vspec.valid vtls}) =
  {
    IF.seq_t = S.seq vspec.slot_t;
    IF.length = S.length;
    IF.prefix = SA.prefix;
  }

let contains_app_key (#vspec: verifier_spec_base) (vtls: vspec.vtls_t {vspec.valid vtls})
  : IF.idxfn_t (gen_seq vtls) bool
  = contains_app_key_base vtls

let to_app_record_base (#vspec: verifier_spec_base) (vtls: vspec.vtls_t {vspec.valid vtls})
  (ss: S.seq vspec.slot_t) (i: SA.seq_index ss {contains_app_key vtls ss i})
  = let s = S.index ss i in
    let open Zeta.GenKey in
    let AppK ak, AppV av = Some?.v (vspec.get s vtls) in
    ak,av

let to_app_record (#vspec: verifier_spec_base) (vtls: vspec.vtls_t {vspec.valid vtls})
  : IF.cond_idxfn_t (app_record vspec.app.adm) (contains_app_key vtls)
  = to_app_record_base vtls

let get_record_set
  (#vspec: verifier_spec_base)
  (ss: S.seq (vspec.slot_t))
  (vtls: vspec.vtls_t {vspec.valid vtls})
  : Tot (let record_t = app_record vspec.app.adm in
         ors: option (S.seq record_t) {Some? ors ==> (let rs = Some?.v ors in
                                       S.length rs = S.length ss /\
                                       SA.distinct_elems ss /\
                                       distinct_keys #vspec.app.adm rs)})
  = let open FStar.Seq in
    let open Zeta.SeqAux in
    let open Zeta.AppSimulate.Helper in
    let fm = IF.to_fm (contains_app_key vtls) (to_app_record vtls) in
    let rs = IF.filter_map fm ss in
    if distinct_elems_comp ss && S.length rs = S.length ss && distinct_keys_comp rs then
      Some rs
    else None


#push-options "--fuel 0 --ifuel 1 --query_stats"

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
  = let open FStar.Seq in
    let open Zeta.SeqAux in
    let open Zeta.AppSimulate.Helper in
    let fm = IF.to_fm (contains_app_key vtls) (to_app_record vtls) in
    let rs = IF.filter_map fm ss in
    assert(distinct_elems ss /\ S.length rs = S.length ss /\ distinct_keys rs);
    IF.lemma_idx2fidx_idem (contains_app_key vtls) ss i

#pop-options

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

let runapp_doesnot_change_slot_key
  (#vspec: verifier_spec)
  (e: verifier_log_entry vspec {is_appfn e})
  (vs: vspec.vtls_t)
  (s: vspec.slot_t)
  : Lemma (requires (let RunApp _ _ ss = e in
                     vspec.valid (verify_step e vs)))
          (ensures (let vs' = verify_step e vs in
                    Some? (vspec.get s vs) ==>
                    Some? (vspec.get s vs') /\
                    key_of (Some?.v (vspec.get s vs)) =
                    key_of (Some?.v (vspec.get s vs'))))
  = admit()

let runapp_implies_slot_contains
  (#vspec: verifier_spec)
  (e: verifier_log_entry vspec {is_appfn e})
  (vs: vspec.vtls_t)
  (s: vspec.slot_t)
  : Lemma (requires (vspec.valid (verify_step e vs)))
          (ensures (let RunApp _ _ ss = e in
                    S.mem s ss ==> Some? (vspec.get s vs)))
  = admit()
