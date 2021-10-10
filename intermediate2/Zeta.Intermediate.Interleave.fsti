module Zeta.Intermediate.Interleave

open FStar.Seq
open Zeta.SeqAux
open Zeta.Interleave
open Zeta.Intermediate.VerifierConfig
open Zeta.Intermediate.Store
open Zeta.Intermediate.Verifier
open Zeta.Intermediate.Logs
open Zeta.Generic.Interleave

module I = Zeta.Interleave
module SA = Zeta.SeqAux
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

(* every store of every prefix of every thread is a map *)
val forall_store_ismap (#vcfg:_) (il: verifiable_log vcfg): prop

val elim_forall_store_ismap (#vcfg:_) (il: verifiable_log vcfg) (t:nat{t < vcfg.thread_count})
  : Lemma (ensures (forall_store_ismap il ==> (let st = thread_store t il in
                                               is_map st)))

val forall_store_ismap_prefix (#vcfg:_) (il: verifiable_log vcfg) (l:nat{l <= length il})
  : Lemma (ensures (forall_store_ismap il ==> (let il' = prefix il l in
                                               forall_store_ismap il')))
