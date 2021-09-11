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

(* for an eac ts log, if the eac state of a key k is instore, the count of blum evicts
 * is the same of blum adds for that key for any epoch *)
val lemma_evict_add_count_same
  (#app #n:_)
  (ep: epoch)
  (il: eac_log app n)
  (gk:key app):
  Lemma (requires (let bk = to_base_key gk in
                   let es = eac_state_of_key bk il in
                   EACInStore? es))
        (ensures (size (k_add_set ep gk il) = size (k_evict_set ep gk il)))

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
  : (be':ms_hashfn_dom app{let ep = be'.t.e in
                           let as = add_set ep itsl in
                           let es = evict_set ep itsl in
                           let be = blum_add_elem itsl i in
                           mem be' as > mem be' es /\
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
  : (be':ms_hashfn_dom app{let ep = be'.t.e in
                           let as = add_set ep itsl in
                           let es = evict_set ep itsl in
                           let be = blum_add_elem itsl i in
                           mem be' as > mem be' es /\
                           be.t.e = ep})

val eac_evictedb_addb_diff_elem
  (#app #n:_)
  (itsl: its_log app n)
  (i: seq_index itsl{let itsli = prefix itsl i in
                     let itsli' = prefix itsl (i + 1) in
                     is_blum_add itsl i /\
                     is_eac itsli /\
                     not (is_eac itsli') /\
                     (let e = index itsl i in
                      let k = add_slot e in
                      let es = eac_state_of_key k itsli in
                      EACEvictedBlum? es)})
  : (be':ms_hashfn_dom app{let ep = be'.t.e in
                           let as = add_set ep itsl in
                           let es = evict_set ep itsl in
                           let be = blum_add_elem itsl i in
                           mem be' as > mem be' es /\
                           be.t.e = ep})

(* when the eac store is evicted, there exists a previous evict *)
val previous_evict_of_eac_evicted
  (#app #n:_)
  (itsl: eac_log app n)
  (k: base_key {EACEvictedBlum? (eac_state_of_key k itsl)})
  : i:seq_index itsl{is_blum_evict itsl i /\
                     (let be = blum_evict_elem itsl i in
                      let EACEvictedBlum gk v t j = eac_state_of_key k itsl in
                      let gk',v' = be.r in
                      let open Zeta.MultiSetHashDomain in
                      gk = gk' /\ v = v' /\ be.t = t /\ be.tid = j)}
