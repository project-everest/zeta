module Zeta.Generic.Thread

open Zeta.Time
open Zeta.MultiSetHashDomain
open Zeta.GenericVerifier

module S = FStar.Seq
module SA = Zeta.SeqAux
module MSD = Zeta.MultiSetHashDomain

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

val blum_add_seq (#vspec: verifier_spec) (ep: epoch) (tl: verifiable_log vspec):
  S.seq (ms_hashfn_dom vspec.app)

(* map a blum add to an index of the add sequence of the epoch of the add *)
val add_seq_map
  (#vspec: verifier_spec)
  (tl: verifiable_log vspec)
  (i: seq_index tl {is_blum_add (index tl i)}):
  (let be = blum_add_elem (index tl i) in
   let ep = epoch_of be in
   let add_seq = blum_add_seq ep tl in
   j: SA.seq_index add_seq{S.index add_seq j = be})

val add_seq_inv_map
  (#vspec: verifier_spec)
  (ep: epoch)
  (tl: verifiable_log vspec)
  (j: SA.seq_index (blum_add_seq ep tl)):
  (i: seq_index tl {is_blum_add (index tl i) /\
                    blum_add_elem (index tl i) = S.index (blum_add_seq ep tl) j /\
                    epoch_of (blum_add_elem (index tl i)) = ep /\
                    add_seq_map tl i = j})

val lemma_add_seq_inv (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl{is_blum_add (index tl i)}):
  Lemma (ensures (let be = blum_add_elem (index tl i) in
                  let ep = epoch_of be in
                  add_seq_inv_map ep tl (add_seq_map tl i) = i))
        [SMTPat (add_seq_map tl i)]

val blum_evict_seq (#vspec:_) (ep: epoch) (tl: verifiable_log vspec): S.seq (ms_hashfn_dom vspec.app)
