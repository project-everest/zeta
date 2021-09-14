module Zeta.High.Thread

open Zeta.GenKey
open Zeta.GenericVerifier
open Zeta.High.Verifier
open Zeta.Generic.Thread

let verifiable_log (app:_)
  = Zeta.Generic.Thread.verifiable_log (high_verifier_spec app)

let store (#app:_) (tl: verifiable_log app)
  = let vs = state tl in
    vs.st

let store_pre (#app:_) (tl: verifiable_log app) (i: seq_index tl)
  = let tl' = prefix tl i in
    store tl'

let store_post (#app:_) (tl: verifiable_log app) (i: seq_index tl)
  = let tl' = prefix tl (i+1) in
    store tl'

val lemma_blum_add_elem_props (#app:_) (tl: verifiable_log app) (i: seq_index tl {is_blum_add tl i})
  : Lemma (ensures (let open Zeta.MultiSetHashDomain in
                    let be = blum_add_elem tl i in
                    let gk,gv = be.r in
                    add_slot (index tl i) = to_base_key gk))
          [SMTPat (blum_add_elem tl i)]

val lemma_blum_evict_elem_key (#app:_) (tl: verifiable_log app) (i: seq_index tl {is_blum_evict tl i})
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
          [SMTPat (blum_evict_elem tl i)]
