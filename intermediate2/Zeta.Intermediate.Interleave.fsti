module Zeta.Intermediate.Interleave

open FStar.Seq
open Zeta.SeqAux
open Zeta.Interleave
open Zeta.Time
open Zeta.Intermediate.VerifierConfig
open Zeta.Intermediate.Store
open Zeta.Intermediate.Verifier
open Zeta.Intermediate.Logs
open Zeta.Intermediate.StateRel
open Zeta.Generic.Interleave

module I = Zeta.Interleave
module SA = Zeta.SeqAux
module GG = Zeta.Generic.Global
module GI = Zeta.Generic.Interleave
module HI = Zeta.High.Interleave
module IV = Zeta.Intermediate.Verifier
module IG = Zeta.Intermediate.Global

let ilog (vcfg: verifier_config) =
  Zeta.Generic.Interleave.ilog (int_verifier_spec vcfg) (vcfg.thread_count)

let verifiable_log (vcfg: verifier_config)
  = il: ilog vcfg {verifiable il}

let thread_store (#vcfg:_) (tid:nat{tid < vcfg.thread_count}) (il: verifiable_log vcfg)
  = let vs = thread_state tid il in
    vs.st

let thread_store_pre (#vcfg:_) (tid: nat{tid < vcfg.thread_count}) (il: verifiable_log vcfg) (i: seq_index il)
  = let vs = thread_state_pre tid il i in
    vs.st

let thread_store_post (#vcfg:_) (tid: nat{tid < vcfg.thread_count}) (il: verifiable_log vcfg) (i: seq_index il)
  = let vs = thread_state_post tid il i in
    vs.st

let to_logk_entry (#vcfg:_) (il: verifiable_log vcfg) (i: seq_index il)
  : logK_entry vcfg.app
  = let gl = to_glog il in
    let ti = i2s_map il i in
    IG.to_logk_entry gl ti

let same_shape #a #b #n (il: interleaving a n) (il': interleaving b n)
  = let ss = s_seq il in
    let ss' = s_seq il' in
    (forall (i:SA.seq_index ss). Seq.length (Seq.index ss i) == Seq.length (Seq.index ss i))

val to_logk (#vcfg:_) (il: verifiable_log vcfg)
  : hil:HI.ilog vcfg.app vcfg.thread_count {same_shape il hil}

val lemma_to_logk_length (#vcfg:_) (il: verifiable_log vcfg)
  : Lemma (ensures (length il = length (to_logk il)))
          [SMTPat (to_logk il)]

val lemma_to_logk_src (#vcfg:_) (il: verifiable_log vcfg) (i: seq_index il)
  : Lemma (ensures src il i == src (to_logk il) i)
          [SMTPat (src il i)]

val lemma_to_logk_index (#vcfg:_) (ils: verifiable_log vcfg) (i: seq_index ils)
  : Lemma (ensures (index (to_logk ils) i == to_logk_entry ils i))
          [SMTPat (index ils i)]

val lemma_to_logk_prefix_commute (#vcfg:_)
  (il:verifiable_log vcfg)
  (i:nat{i <= length il})
  : Lemma (to_logk (prefix il i) == SA.prefix (to_logk il) i)
          [SMTPat (prefix il i)]

(* every store of every prefix of every thread is a map *)
val forall_store_ismap (#vcfg:_) (il: verifiable_log vcfg): prop

val elim_forall_store_ismap (#vcfg:_) (il: verifiable_log vcfg) (t:nat{t < vcfg.thread_count})
  : Lemma (ensures (forall_store_ismap il ==> (let st = thread_store t il in
                                               is_map st)))

val forall_store_ismap_prefix (#vcfg:_) (il: verifiable_log vcfg) (l:nat{l <= length il})
  : Lemma (ensures (forall_store_ismap il ==> (let il' = prefix il l in
                                               forall_store_ismap il')))
          [SMTPat (prefix il l)]

val lemma_forall_store_ismap_snoc (#vcfg:_) (il: verifiable_log vcfg{length il > 0})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     let t = src il i in
                     forall_store_ismap il' /\
                     is_map (thread_store t il)))
          (ensures forall_store_ismap il)

(* every state of every prefix is related to high-level state *)
val forall_vtls_rel (#vcfg:_) (il: verifiable_log vcfg): prop

(* vtls_rel implies every high-level thread is valid, so (to_logk il) is verifiable *)
val lemma_forall_vtls_rel_implies_spec_verifiable (#vcfg:_) (il: verifiable_log vcfg)
  : Lemma (ensures (let ilk = to_logk il in
                    forall_vtls_rel il ==> GI.verifiable (to_logk il)))
          [SMTPat (forall_vtls_rel il)]

val elim_forall_vtls_rel (#vcfg:_) (il: verifiable_log vcfg) (t: nat{t < vcfg.thread_count})
  : Lemma (requires (forall_vtls_rel il))
          (ensures (let ilk = to_logk il in
                    let vsi = thread_state t il in
                    let vst = thread_state t ilk in
                    vtls_rel vsi vst))

val forall_vtls_rel_prefix (#vcfg:_) (il: verifiable_log vcfg) (i:nat{i <= length il})
  : Lemma (ensures (let il' = prefix il i in
                    forall_vtls_rel il ==> forall_vtls_rel il'))
          [SMTPat (prefix il i)]

val forall_vtls_rel_snoc (#vcfg:_) (il: verifiable_log vcfg{length il > 0})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     let ilk = to_logk il in
                     let t = src il i in
                     forall_vtls_rel il' /\
                     vtls_rel (thread_state t il) (thread_state t ilk)))
          (ensures (forall_vtls_rel il))

val lemma_vtls_rel_implies_ms_verifiable (#vcfg:_) (ep: epoch) (ils:verifiable_log vcfg)
  : Lemma (requires (forall_vtls_rel ils))
          (ensures (let ilk = to_logk ils in
                    GG.aems_equal_upto ep (to_glog ils) ==> GG.aems_equal_upto ep (to_glog ilk)))

let spec_rel (#vcfg:_) (il: verifiable_log vcfg)
  = forall_store_ismap il /\
    forall_vtls_rel il

val lemma_empty_implies_spec_rel (#vcfg:_) (il:verifiable_log vcfg)
  : Lemma (ensures (length il = 0 ==> spec_rel il))

val lemma_spec_rel_implies_prefix_spec_rel (#vcfg:_) (il:verifiable_log vcfg) (i:nat{i <= length il})
 : Lemma (requires spec_rel il)
         (ensures (let il' = prefix il i in
                   spec_rel il'))
         [SMTPat (prefix il i)]

val lemma_spec_rel_implies_appfn_identical (#vcfg:_) (il: verifiable_log vcfg {spec_rel il})
  : Lemma (ensures (let gl = to_glog il in
                    let ilk = to_logk il in
                    let glk = to_glog ilk in
                    GG.app_fcrs gl = GG.app_fcrs glk))
          [SMTPat (spec_rel il)]
