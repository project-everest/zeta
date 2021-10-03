module Zeta.High.Verifier

let contains_only_app_keys_comp (#app:_) (st: store_t app) (ks: S.seq base_key)
  : b:bool { b <==> contains_only_app_keys st ks }
  = let open Zeta.SeqIdx in
    not (exists_elems_with_prop_comp (fun k -> not (contains_app_key st k)) ks)

let puts_store (#app:_)
  (st: store_t app)
  (ks: S.seq base_key)
  (ws: S.seq (app_value_nullable app.adm))
  : store_t app
  = if contains_only_app_keys_comp st ks && S.length ws = S.length ks then
      fun k -> if S.mem k ks then
               let i = S.index_mem k ks in
               let am = add_method_of st k in
               let gk = stored_key st k in
               let gv = AppV (S.index ws i) in
               let r = gk,gv in
               Some ({r; am})
             else
               st k
    else st

let puts (#app:_)
  (vs: vtls_t app{vs.valid})
  (ks: S.seq base_key)
  (ws: S.seq (app_value_nullable app.adm))
  : vs': vtls_t app{vs'.valid}
  = let st = puts_store vs.st ks ws in
    update_thread_store vs st

let clock_is_monotonic
  (#app:_)
  (e: GV.verifier_log_entry (high_verifier_spec_base app))
  (vs: vtls_t app)
  : Lemma (ensures (let vs_post = GV.verify_step e vs in
                    vs_post.valid ==> vs.clock `ts_leq` vs_post.clock))
  = ()

let lemma_high_verifier_clock_monotonic_prop (app:_)
  : Lemma (ensures (GV.clock_monotonic_prop (high_verifier_spec_base app)))
  = FStar.Classical.forall_intro_2 (clock_is_monotonic #app)

let thread_id_is_constant
  (#app:_)
  (e: GV.verifier_log_entry (high_verifier_spec_base app))
  (vs: vtls_t app)
  : Lemma (ensures (let vs_post = GV.verify_step e vs in
                    vs.tid = vs_post.tid))
  = ()

let lemma_high_verifier_thread_id_const_prop (app:_)
  : Lemma (ensures (GV.thread_id_constant_prop (high_verifier_spec_base app)))
  = FStar.Classical.forall_intro_2 (thread_id_is_constant #app)

let evict_prop
  (#app:_)
  (e: GV.verifier_log_entry (high_verifier_spec_base app))
  (vs: vtls_t app)
  : Lemma (ensures (let vs_post = GV.verify_step e vs in
                    GV.is_evict e ==>
                    vs_post.valid ==>
                    store_contains vs.st (GV.evict_slot e) /\
                    not (store_contains vs_post.st (GV.evict_slot e))))
  = ()

let lemma_high_verifier_evict_prop (app:_)
  : Lemma (ensures (GV.evict_prop (high_verifier_spec_base app)))
  = FStar.Classical.forall_intro_2 (evict_prop #app)

let add_prop
  (#app:_)
  (e: GV.verifier_log_entry (high_verifier_spec_base app))
  (vs: vtls_t app)
  : Lemma (ensures (let vs_post = GV.verify_step e vs in
                    GV.is_add e ==>
                    vs_post.valid ==>
                    not (store_contains vs.st (GV.add_slot e)) /\
                    store_contains vs_post.st (GV.add_slot e)))
  = ()

let lemma_high_verifier_add_prop (app:_)
  : Lemma (ensures (GV.add_prop (high_verifier_spec_base app)))
  = FStar.Classical.forall_intro_2 (add_prop #app)

let addb_prop
  (#app:_)
  (e: GV.verifier_log_entry (high_verifier_spec_base app))
  (vs: vtls_t app)
  : Lemma (ensures (let vs_post = GV.verify_step e vs in
                    GV.is_blum_add e ==>
                    vs_post.valid ==>
                    GV.blum_add_timestamp e `ts_lt` vs_post.clock))
  = ()

let lemma_high_verifier_addb_prop (app:_)
  : Lemma (ensures (GV.addb_prop (high_verifier_spec_base app)))
  = FStar.Classical.forall_intro_2 (addb_prop #app)

let evictb_prop
  (#app:_)
  (e: GV.verifier_log_entry (high_verifier_spec_base app))
  (vs: vtls_t app)
  : Lemma (ensures (let vs_post = GV.verify_step e vs in
                    GV.is_blum_evict e ==>
                    vs_post.valid ==>
                    vs.clock `ts_lt` vs_post.clock))
  = ()

let lemma_high_verifier_evictb_prop (app:_)
  : Lemma (ensures (GV.evictb_prop (high_verifier_spec_base app)))
  = FStar.Classical.forall_intro_2 (evictb_prop #app)

let lemma_high_verifier (aprm: app_params)
  : Lemma (ensures (GV.clock_monotonic_prop (high_verifier_spec_base aprm) /\
                    GV.thread_id_constant_prop (high_verifier_spec_base aprm) /\
                    GV.evict_prop (high_verifier_spec_base aprm) /\
                    GV.add_prop (high_verifier_spec_base aprm) /\
                    GV.addb_prop (high_verifier_spec_base aprm) /\
                    GV.evictb_prop (high_verifier_spec_base aprm)))
  = lemma_high_verifier_clock_monotonic_prop aprm;
    lemma_high_verifier_thread_id_const_prop aprm;
    lemma_high_verifier_evict_prop aprm;
    lemma_high_verifier_add_prop aprm;
    lemma_high_verifier_addb_prop aprm;
    lemma_high_verifier_evictb_prop aprm

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
  = ()

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
  = ()

#push-options "--fuel 0 --ifuel 1"

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
  = let GV.RunApp _ _ ks = e in
    let vs_post = GV.verify_step e vs in
    if vs_post.valid && S.mem k ks then (
      let i = S.index_mem k ks in
      ()
    )

#pop-options

let runapp_doesnot_change_slot_emptiness
  (#app: _)
  (e: vlog_entry app {GV.is_appfn e})
  (vs: vtls_t _)
  (k: base_key)
  : Lemma
          (ensures (let vs_post = GV.verify_step e vs in
                    vs_post.valid ==>
                    ((store_contains vs.st k) <==> (store_contains vs_post.st k))))
  = ()

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
  = ()

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
  = ()
