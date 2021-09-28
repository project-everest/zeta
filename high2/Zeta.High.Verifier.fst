module Zeta.High.Verifier

let lemma_high_verifier (aprm: app_params)
  : Lemma (ensures (GV.clock_monotonic_prop (high_verifier_spec_base aprm) /\
                    GV.thread_id_constant_prop (high_verifier_spec_base aprm) /\
                    GV.evict_prop (high_verifier_spec_base aprm) /\
                    GV.add_prop (high_verifier_spec_base aprm)))
  = admit()

let runapp_doesnot_change_store_addmethod
  (#app:_)
  (ki: base_key)
  (e: vlog_entry app {Zeta.GenericVerifier.RunApp? e})
  (vs: vtls_t app)
  : Lemma (ensures (let vs_post = Zeta.GenericVerifier.verify_step e vs in
                    vs_post.valid ==>
                    store_contains vs.st ki ==>
                    store_contains vs_post.st ki /\
                    add_method_of vs.st ki = add_method_of vs_post.st ki))
  = admit()
