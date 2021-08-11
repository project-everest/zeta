module Zeta.Generic.Thread

open Zeta.GenericVerifier
open Zeta.Time

module S = FStar.Seq
module SA = Zeta.SeqAux

(* a verifier log attached to a thread id *)
let tid_vlog (vspec: verifier_spec) = thread_id & verifier_log vspec

let length #vspec (tl: tid_vlog vspec) =
  let _, l = tl in
  S.length l

let seq_index #vspec (tl: tid_vlog vspec) = i:nat {i < length tl}

let index #vspec (tl: tid_vlog vspec) (i: seq_index tl) =
  let _, l = tl in
  S.index l i

let prefix #vspec (tl: tid_vlog vspec) (i: nat {i <= length tl}): tid_vlog _ =
  let tid, l = tl in
  tid, SA.prefix l i

let verify #vspec (tl: tid_vlog vspec): vspec.vtls_t =
  let tid, l = tl in
  Zeta.GenericVerifier.verify tid l

let verifiable #vspec (tl: tid_vlog vspec) = vspec.valid (verify tl)

let verifiable_log vspec = tl: tid_vlog vspec { verifiable tl }

(* if a thread log is verifiable, its prefix is verifiable *)
val verifiable_implies_prefix_verifiable (#vspec:verifier_spec)
  (tl:verifiable_log vspec) (i:nat{i <= length tl}):
  Lemma (ensures (verifiable (prefix tl i)))
        [SMTPat (prefix tl i)]

(* clock after processing i entries of the log *)
let clock #vspec (tl: verifiable_log vspec) (i: nat { i <= length tl }) =
  vspec.clock (verify tl)

(* clock is monotonic *)
val lemma_clock_monotonic (#vspec:verifier_spec)
  (tl: verifiable_log vspec) (i:nat) (j:nat {j >= i /\ j <= length tl}):
  Lemma (clock tl i `ts_leq` clock tl j)

(* the thread id in the state is always the one specified in the parameter *)
val lemma_thread_id_state (#vspec:verifier_spec) (tl: verifiable_log vspec):
  Lemma (ensures (let tid, _ = tl in
                  vspec.tid (verify tl) = tid))

(* the verifier state after processing i entries *)
let state_at #vspec (tl: verifiable_log vspec) (i:nat{i <= length tl}) =
  (verify (prefix tl i))

(* the state after processing i'th entry is obtained by applying the verify
 * step to the state before processing the i'th entry *)
val lemma_state_transition (#vspec:verifier_spec) (tl: verifiable_log vspec) (i: seq_index tl):
  Lemma (ensures (state_at tl (i + 1) ==
                  verify_step (index tl i) (state_at tl i)))
        [SMTPat (verify_step (index tl i) (state_at tl i))]
