module Zeta.High.Blum

open Zeta.SeqAux
open Zeta.Interleave
open Zeta.MultiSet
open Zeta.MultiSetHashDomain
open Zeta.Time
open Zeta.Key
open Zeta.GenKey
open Zeta.EAC
open Zeta.GenericVerifier
open Zeta.Generic.Interleave
open Zeta.Generic.Blum
open Zeta.High.Interleave
open Zeta.High.TSLog

val eac_instore_addb_diff_elem
  (#app #n:_)
  (itsl: its_log app n)
  (i: seq_index itsl{let itsli = prefix itsl i in
                     is_blum_add itsl i /\
                     is_eac itsli /\
                     (let e = index itsl i in
                      let k = add_slot e in
                      let es = eac_state_of_key k itsli in
                      EACInStore? es)})
  : GTot (be':ms_hashfn_dom app{let ep = be'.t.e in
                           let a_s = add_set ep itsl in
                           let es = evict_set ep itsl in
                           let be = blum_add_elem itsl i in
                           mem be' a_s > mem be' es /\
                           be.t.e = ep})

val eac_evictedm_addb_diff_elem
  (#app #n:_)
  (itsl: its_log app n)
  (i:seq_index itsl{let itsli = prefix itsl i in
                    is_blum_add itsl i /\
                    is_eac itsli /\
                    (let e = index itsl i in
                     let k = add_slot e in
                     let es = eac_state_of_key k itsli in
                     EACEvictedMerkle? es)})
  : GTot (be':ms_hashfn_dom app{let ep = be'.t.e in
                           let a_s = add_set ep itsl in
                           let es = evict_set ep itsl in
                           let be = blum_add_elem itsl i in
                           mem be' a_s > mem be' es /\
                           be.t.e = ep})

val eac_evictedb_addb_diff_elem
  (#app #n:_)
  (itsl: neac_log app n {let i = eac_boundary itsl in
                         let k = eac_fail_key itsl in
                         Zeta.Generic.TSLog.clock_sorted itsl /\
                         is_blum_add itsl i /\
                         EACEvictedBlum? (eac_state_of_key_pre k itsl i)})
  : GTot (be':ms_hashfn_dom app{let i = eac_boundary itsl in
                           let ep = be'.t.e in
                           let a_s = add_set ep itsl in
                           let es = evict_set ep itsl in
                           let be = blum_add_elem itsl i in
                           mem be' a_s > mem be' es /\
                           be.t.e = ep})

val eac_add_set_mem_atleast_evict_set_mem
  (#app #n:_)
  (il: eac_log app n)
  (t:nat {t < n})
  (be: ms_hashfn_dom app)
  : Lemma (requires (let gk,_ = be.r in
                     let k = to_base_key gk in
                     Zeta.High.Verifier.store_contains (thread_store t il) k))
          (ensures (mem be (add_set be.t.e il) >= mem be (evict_set be.t.e il)))
