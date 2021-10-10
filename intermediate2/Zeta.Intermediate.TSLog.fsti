module Zeta.Intermediate.TSLog

open FStar.Seq
open Zeta.Interleave
open Zeta.Generic.Interleave
open Zeta.Generic.TSLog
open Zeta.Intermediate.VerifierConfig
open Zeta.Intermediate.Verifier
open Zeta.Intermediate.Interleave

module T = Zeta.Generic.TSLog
module I = Zeta.Interleave
module HT = Zeta.High.TSLog

let its_log (vcfg:_)
  = T.its_log (int_verifier_spec vcfg) (vcfg.thread_count)

let same_shape #a #b #n (il:I.interleaving a n) (il':I.interleaving b n)
  = let ss = s_seq il in
    let ss' = s_seq il' in
    (forall (i:nat{i < n}). Seq.length (Seq.index ss i) == Seq.length (Seq.index ss i))

val to_logk (#vcfg:_) (il: its_log vcfg)
  : sil:HT.its_log vcfg.app vcfg.thread_count { same_shape il sil }

val lemma_to_logk_length (#vcfg:_) (il: its_log vcfg)
  : Lemma (ensures (length il = length (to_logk il)))
          [SMTPat (to_logk il)]

val lemma_to_logk_prefix_commute (#vcfg:_) (il:its_log vcfg) (i:nat{i <= length il})
  : Lemma (to_logk (prefix il i) == prefix (to_logk il) i)
          [SMTPat (prefix il i)]

val lemma_to_logk_src (#vcfg:_) (il: its_log vcfg) (i: seq_index il)
  : Lemma (ensures (src il i = src (to_logk il) i))
          [SMTPat (src il i)]
