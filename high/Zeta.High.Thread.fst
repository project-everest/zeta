module Zeta.High.Thread

#push-options "--fuel 0 --ifuel 1"

let lemma_blum_add_elem_props (#app:_) (tl: verifiable_log app) (i: seq_index tl {is_blum_add tl i})
  : Lemma (ensures (let open Zeta.MultiSetHashDomain in
                    let be = blum_add_elem tl i in
                    let gk,gv = be.r in
                    add_slot (index tl i) = to_base_key gk))
  = lemma_state_transition tl i

let lemma_blum_evict_elem_key (#app:_) (tl: verifiable_log app) (i: seq_index tl {is_blum_evict tl i})
  : Lemma (ensures (let open Zeta.MultiSetHashDomain in
                    let st_pre = store_pre tl i in
                    let be = blum_evict_elem tl i in
                    let gk,gv = be.r in
                    let k = evict_slot (index tl i) in
                    let open Zeta.MultiSetHashDomain in
                    k = to_base_key gk /\
                    gk = stored_key st_pre k /\
                    gv = stored_value st_pre k /\
                    be.t = blum_evict_timestamp (index tl i) /\
                    be.tid = fst tl))
  = ()

let not_refs_implies_store_unchanged_runapp  (#app:_) (ki:Zeta.Key.base_key)
  (tl: verifiable_log app) (i:seq_index tl)
  : Lemma (requires (let e = index tl i in
                     let st_pre = store_pre tl i in
                     let st_post = store_post tl i in
                     RunApp? (index tl i) /\
                     not (e `exp_refs_key` ki) /\
                     store_contains st_pre ki))
          (ensures (let e = index tl i in
                    let st_pre = store_pre tl i in
                    let st_post = store_post tl i in
                    store_contains st_post ki /\ st_pre ki == st_post ki))
  = let e = index tl i in
    let vs_pre = state_pre tl i in
    let vs_post = state_post tl i in

    lemma_state_transition tl i;
    assert(vs_post == verify_step e vs_pre);

    runapp_doesnot_change_nonref_slots e vs_pre ki;
    assert((Some?.v (vs_pre.st ki)).r = (Some?.v (vs_post.st ki)).r);
    runapp_doesnot_change_store_addmethod ki e vs_pre

#push-options "--z3rlimit_factor 3"

let not_refs_implies_store_unchanged  (#app:_) (ki:Zeta.Key.base_key)
  (tl: verifiable_log app) (i:seq_index tl)
  : Lemma (ensures (let e = index tl i in
                    let st_pre = store_pre tl i in
                    let st_post = store_post tl i in
                    not (e `exp_refs_key` ki) ==>
                    store_contains st_pre ki ==>
                    (store_contains st_post ki /\ st_pre ki == st_post ki)))
  = let e = index tl i in
    let vs_pre = state_pre tl i in
    let vs_post = state_post tl i in

    lemma_state_transition tl i;
    assert(vs_post == verify_step e vs_pre);

    if not (e `exp_refs_key` ki) && store_contains vs_pre.st ki then (
      match e with
      | RunApp _ _ _ -> not_refs_implies_store_unchanged_runapp ki tl i
      | _ -> ())
