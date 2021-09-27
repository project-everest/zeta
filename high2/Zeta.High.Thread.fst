module Zeta.High.Thread

let lemma_blum_add_elem_props (#app:_) (tl: verifiable_log app) (i: seq_index tl {is_blum_add tl i})
  : Lemma (ensures (let open Zeta.MultiSetHashDomain in
                    let be = blum_add_elem tl i in
                    let gk,gv = be.r in
                    add_slot (index tl i) = to_base_key gk))
  = admit()

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
  = admit()

let not_refs_implies_store_unchanged  (#app:_) (k:Zeta.Key.base_key)
  (tl: verifiable_log app) (i:seq_index tl)
  : Lemma (ensures (let e = index tl i in
                    let st_pre = store_pre tl i in
                    let st_post = store_post tl i in
                    not (e `exp_refs_key` k) ==>
                    store_contains st_pre k ==>
                    (store_contains st_post k /\ st_pre k == st_post k)))
  = admit()
