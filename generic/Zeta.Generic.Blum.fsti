module Zeta.Generic.Blum

open Zeta.Interleave
open Zeta.MultiSet
open Zeta.Time
open Zeta.MultiSetHashDomain
open Zeta.GenericVerifier
open Zeta.Generic.Interleave
open Zeta.Generic.TSLog

module S = FStar.Seq
module SA = Zeta.SeqAux
module G = Zeta.Generic.Global

val add_il (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n)
  : interleaving (ms_hashfn_dom vspec.app) n

let add_seq (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n)
  : S.seq (ms_hashfn_dom vspec.app)
  = i_seq (add_il ep il)

let add_set #vspec #n (ep: epoch) (il: verifiable_log vspec n)
  : mset_ms_hashfn_dom vspec.app
  = seq2mset (add_seq ep il)

val evict_il (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n)
  : interleaving (ms_hashfn_dom vspec.app) n

let evict_seq (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n)
  : S.seq (ms_hashfn_dom vspec.app)
  = i_seq (evict_il ep il)

let evict_set #vspec #n (ep: epoch) (il: verifiable_log vspec n)
  : mset_ms_hashfn_dom vspec.app
  = seq2mset (evict_seq ep il)

let aems_equal_upto #vspec #n (epmax: epoch) (il: verifiable_log vspec n)
  = forall (ep: epoch). ep <= epmax ==> add_set ep il == evict_set ep il

val lemma_add_evict_set_identical_glog (#vspec #n:_) (epmax: epoch) (il: verifiable_log vspec n)
  : Lemma (ensures (aems_equal_upto epmax il <==> G.aems_equal_upto epmax (to_glog il)))

val add_set_contains_each_add_elem (#vspec #n:_) (il: verifiable_log vspec n) (i: seq_index il{is_blum_add il i})
  : Lemma (ensures (let be = blum_add_elem il i in
                    let ep = be.t.e in
                    add_set ep il `contains` be))
          [SMTPat (blum_add_elem il i)]

val some_add_elem_idx
  (#vspec #n:_)
  (il: verifiable_log vspec n)
  (be: ms_hashfn_dom vspec.app {let ep = be.t.e in
                                add_set ep il `contains` be})
  : i: seq_index il {is_blum_add il i /\ be = blum_add_elem il i}

val evict_set_contains_each_evict_elem (#vspec #n:_) (il: verifiable_log vspec n) (i: seq_index il{is_blum_evict il i})
  : Lemma (ensures (let be = blum_evict_elem il i in
                    let ep = be.t.e in
                    evict_set ep il `contains` be))
          [SMTPat (blum_evict_elem il i)]

val evict_set_is_a_set (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n)
  : Lemma (ensures (is_set (evict_set ep il)) )

val evict_elem_idx
  (#vspec #n:_)
  (il: verifiable_log vspec n)
  (be: ms_hashfn_dom vspec.app {let ep = be.t.e in
                                evict_set ep il `contains` be})
  : i: seq_index il {is_blum_evict il i /\ be = blum_evict_elem il i}

val lemma_evict_before_add (#vspec #n:_) (itsl: its_log vspec n) (i:seq_index itsl{is_blum_add itsl i}):
  Lemma (ensures (let be = blum_add_elem itsl i in
                  let ep = be.t.e in
                  not (evict_set ep itsl `contains` be) \/
                  evict_elem_idx itsl be < i))
