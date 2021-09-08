module Zeta.GenericVerifier

let get_record_set (#vspec: verifier_spec_base) (ss: S.seq (vspec.slot_t)) (vtls: vspec.vtls_t {vspec.valid vtls}):
  (let record_t = app_record vspec.app.adm in
   ors: option (S.seq record_t) {Some? ors ==> (let rs = Some?.v ors in
                                                S.length rs = S.length ss /\
                                                SA.distinct_elems ss /\
                                                distinct_keys #vspec.app.adm rs)})
  = admit()

let update_record_set (#vspec: verifier_spec_base)
                      (ss: S.seq (vspec.slot_t))
                      (vtls: vspec.vtls_t {vspec.valid vtls /\ Some? (get_record_set ss vtls)})
                      (ws: S.seq (app_value_nullable vspec.app.adm) {let rs = get_record_set_succ ss vtls in
                                                                     S.length ws = S.length rs}): vspec.vtls_t
  = admit()
