module Zeta.Intermediate.Blum

open Zeta.Time
open Zeta.Interleave
open Zeta.Generic.Interleave
open Zeta.Generic.Blum
open Zeta.High.Interleave
open Zeta.Intermediate.Interleave

module GG = Zeta.Generic.Global

val lemma_spec_rel_implies_same_add_elem (#vcfg:_)
  (il: verifiable_log vcfg {spec_rel il})
  (i: seq_index il {is_blum_add il i})
  : Lemma (ensures (let ilk = to_logk il in
                    is_blum_add ilk i /\
                    blum_add_elem il i = blum_add_elem ilk i))
          [SMTPat (blum_add_elem il i)]

val lemma_spec_rel_implies_same_evict_elem (#vcfg:_)
  (il: verifiable_log vcfg {spec_rel il})
  (i: seq_index il {is_blum_evict il i})
  : Lemma (ensures (let ilk = to_logk il in
                    is_blum_evict ilk i /\
                    blum_evict_elem il i = blum_evict_elem ilk i))
          [SMTPat (blum_evict_elem il i)]

val lemma_spec_rel_implies_same_add_seq (#vcfg:_) (ep: epoch) (il: verifiable_log vcfg)
  : Lemma (requires (spec_rel il))
          (ensures (let ilk = to_logk il in
                    add_seq ep il == add_seq ep ilk))
          [SMTPat (add_seq ep il)]

val lemma_spec_rel_implies_same_evict_seq (#vcfg:_) (ep: epoch) (il: verifiable_log vcfg)
  : Lemma (requires (spec_rel il))
          (ensures (let ilk = to_logk il in
                    evict_seq ep il == evict_seq ep ilk))
          [SMTPat (evict_seq ep il)]

val lemma_spec_rel_implies_same_add_set (#vcfg:_) (ep: epoch) (il: verifiable_log vcfg)
  : Lemma (requires (spec_rel il))
          (ensures (let ilk = to_logk il in
                    add_set ep il == add_set ep ilk))
          [SMTPat (add_set ep il)]

val lemma_spec_rel_implies_same_evict_set (#vcfg:_) (ep: epoch) (il: verifiable_log vcfg)
  : Lemma (requires (spec_rel il))
          (ensures (let ilk = to_logk il in
                    evict_set ep il == evict_set ep ilk))
          [SMTPat (evict_set ep il)]

