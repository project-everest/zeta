module Zeta.Generic.Thread

open Zeta.Time
open Zeta.MultiSetHashDomain
open Zeta.GenericVerifier

module S = FStar.Seq
module SA = Zeta.SeqAux
module MSD = Zeta.MultiSetHashDomain
module GV = Zeta.GenericVerifier

(* a verifier log attached to a thread id *)
let vlog (vspec: verifier_spec) = thread_id & verifier_log vspec

let length #vspec (tl: vlog vspec) =
  let _, l = tl in
  S.length l

let seq_index #vspec (tl: vlog vspec) = i:nat {i < length tl}

let index #vspec (tl: vlog vspec) (i: seq_index tl) =
  let _, l = tl in
  S.index l i

let prefix #vspec (tl: vlog vspec) (i: nat {i <= length tl}): vlog _ =
  let tid, l = tl in
  tid, SA.prefix l i

let verify #vspec (tl: vlog vspec): vspec.vtls_t =
  let tid, l = tl in
  Zeta.GenericVerifier.verify tid l

let verifiable #vspec (tl: vlog vspec) = vspec.valid (verify tl)

let verifiable_log vspec = tl: vlog vspec { verifiable tl }

(* if a thread log is verifiable, its prefix is verifiable *)
val verifiable_implies_prefix_verifiable (#vspec:verifier_spec)
  (tl:verifiable_log vspec) (i:nat{i <= length tl}):
  Lemma (ensures (verifiable (prefix tl i)))
        [SMTPat (prefix tl i)]

(* the verifier state after processing i entries *)
let state_at #vspec (tl: verifiable_log vspec) (i:nat{i <= length tl}) =
  (verify (prefix tl i))

(* the state after processing i'th entry is obtained by applying the verify
 * step to the state before processing the i'th entry *)
val lemma_state_transition (#vspec:verifier_spec) (tl: verifiable_log vspec) (i: seq_index tl):
  Lemma (ensures (state_at tl (i + 1) ==
                  verify_step (index tl i) (state_at tl i)))
        [SMTPat (verify_step (index tl i) (state_at tl i))]

(* clock after processing i entries of the log *)
let clock #vspec (tl: verifiable_log vspec) (i: seq_index tl) =
  vspec.clock (verify (prefix tl (i+1)))

(* clock is monotonic *)
val lemma_clock_monotonic (#vspec:verifier_spec)
  (tl: verifiable_log vspec) (i:nat) (j: seq_index tl {j >= i}):
  Lemma (ensures (clock tl i `ts_leq` clock tl j))

(* the thread id in the state is always the one specified in the parameter *)
val lemma_thread_id_state (#vspec:verifier_spec) (tl: verifiable_log vspec):
  Lemma (ensures (let tid, _ = tl in
                  vspec.tid (verify tl) = tid))

let is_blum_add #vspec (tl: verifiable_log vspec) (i: seq_index tl)
  = GV.is_blum_add (index tl i)

val blum_add_elem (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl { is_blum_add tl i }): ms_hashfn_dom vspec.app

let is_blum_add_in_epoch #vspec (ep: epoch) (tl: verifiable_log vspec) (i: seq_index tl)
  = is_blum_add tl i &&
    epoch_of (blum_add_elem tl i) = ep

let is_blum_evict #vspec (tl: verifiable_log vspec) (i: seq_index tl)
  = GV.is_blum_evict (index tl i)

val blum_evict_elem (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl { is_blum_evict tl i }):
  ms_hashfn_dom vspec.app

let is_blum_evict_in_epoch #vspec (ep: epoch) (tl: verifiable_log vspec) (i: seq_index tl)
  = is_blum_evict tl i &&
    epoch_of (blum_evict_elem tl i) = ep
