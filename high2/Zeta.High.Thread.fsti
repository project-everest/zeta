module Zeta.High.Thread

open Zeta.GenKey
open Zeta.GenericVerifier
open Zeta.High.Verifier
open Zeta.Generic.Thread

let verifiable_log (app:_)
  = Zeta.Generic.Thread.verifiable_log (high_verifier_spec app)

val lemma_blum_add_elem_key (#app:_) (tl: verifiable_log app) (i: seq_index tl {is_blum_add tl i})
  : Lemma (ensures (let open Zeta.MultiSetHashDomain in
                    let be = blum_add_elem tl i in
                    let gk,_ = be.r in
                    add_slot (index tl i) = to_base_key gk))
          [SMTPat (blum_add_elem tl i)]

val lemma_blum_evict_elem_key (#app:_) (tl: verifiable_log app) (i: seq_index tl {is_blum_evict tl i})
  : Lemma (ensures (let open Zeta.MultiSetHashDomain in
                    let be = blum_evict_elem tl i in
                    let gk,_ = be.r in
                    evict_slot (index tl i) = to_base_key gk))
          [SMTPat (blum_evict_elem tl i)]
