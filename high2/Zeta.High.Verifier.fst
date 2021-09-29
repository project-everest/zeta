module Zeta.High.Verifier

let contains_only_app_keys_comp (#app:_) (st: store_t app) (ks: S.seq base_key)
  : b:bool { b <==> contains_only_app_keys st ks }
  = admit()

let puts (#app:_)
  (vs: vtls_t app{vs.valid})
  (ks: S.seq base_key)
  (ws: S.seq (app_value_nullable app.adm))
  : vs': vtls_t app{vs'.valid}
  = admit()

let lemma_high_verifier (aprm: app_params)
  : Lemma (ensures (GV.clock_monotonic_prop (high_verifier_spec_base aprm) /\
                    GV.thread_id_constant_prop (high_verifier_spec_base aprm) /\
                    GV.evict_prop (high_verifier_spec_base aprm) /\
                    GV.add_prop (high_verifier_spec_base aprm)))
  = admit()

let runapp_doesnot_change_nonref_slots
  (#app: _)
  (e: vlog_entry app {GV.RunApp? e})
  (vs: vtls_t app)
  (k: base_key)
  : Lemma (requires (let GV.RunApp _ _ ks = e in
                     let vs' = GV.verify_step e vs in
                     vs'.valid /\ not (S.mem k ks)))
          (ensures (let vs' = GV.verify_step e vs in
                    vs.st k == vs'.st k))
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

let runapp_implies_store_contains
  (#app: _)
  (e: vlog_entry app {GV.is_appfn e})
  (vs: vtls_t _)
  (k: base_key)
  : Lemma (ensures (let GV.RunApp _ _ ks = e in
                    let vs_post = GV.verify_step e vs in
                    vs_post.valid ==>
                    S.mem k ks ==>
                    (let rs = GV.reads vs ks in
                     let i = S.index_mem k ks in
                     let ak,av = S.index rs i in
                     store_contains vs.st k /\
                     stored_key vs.st k = AppK ak /\
                     stored_value vs.st k = AppV av)))
  = admit()

let runapp_doesnot_change_slot_emptiness
  (#app: _)
  (e: vlog_entry app {GV.is_appfn e})
  (vs: vtls_t _)
  (k: base_key)
  : Lemma
          (ensures (let vs_post = GV.verify_step e vs in
                    vs_post.valid ==>
                    ((store_contains vs.st k) <==> (store_contains vs_post.st k))))
  = admit()

let runapp_doesnot_change_slot_key
  (#app:_)
  (ki: base_key)
  (e: vlog_entry app {Zeta.GenericVerifier.RunApp? e})
  (vs: vtls_t app)
  : Lemma (ensures (let vs_post = Zeta.GenericVerifier.verify_step e vs in
                    vs_post.valid ==>
                    store_contains vs.st ki ==>
                    store_contains vs_post.st ki /\
                    stored_key vs.st ki = stored_key vs_post.st ki))
  = admit()

let puts_valid
  (#app:_)
  (ki: base_key)
  (e: vlog_entry app {GV.is_appfn e})
  (vs: vtls_t app)
  (i:nat)
  : Lemma (ensures (let GV.RunApp f p ks = e in
                    let vs_post = GV.verify_step e vs in
                    vs_post.valid ==>
                    i < S.length ks ==>
                    (let rs = GV.reads vs ks in
                     let fn = appfn f in
                     let _,_,ws = fn p rs in
                     let k = S.index ks i in
                     store_contains vs_post.st k /\
                     stored_value vs_post.st k = AppV (S.index ws i))))
  = admit()
