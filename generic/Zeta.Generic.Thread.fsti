module Zeta.Generic.Thread

open Zeta.Time
open Zeta.MultiSetHashDomain
open Zeta.GenericVerifier
open Zeta.IdxFn

module S = FStar.Seq
module SA = Zeta.SeqAux
module MSD = Zeta.MultiSetHashDomain
module GV = Zeta.GenericVerifier
module IF = Zeta.IdxFn

(* a verifier log attached to a thread id *)
let vlog (vspec: verifier_spec) = thread_id & verifier_log vspec

let length #vspec (tl: vlog vspec) =
  let _, l = tl in
  S.length l

let seq_index #vspec (tl: vlog vspec) = i:nat {i < length tl}

let index #vspec (tl: vlog vspec) (i: seq_index tl) =
  let _, l = tl in
  S.index l i

let prefix_base #vspec (tl: vlog vspec) (i: nat {i <= length tl}): vlog _ =
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
  Lemma (ensures (verifiable (prefix_base tl i)))
        [SMTPat (prefix_base tl i)]

let prefix #vspec (tl: verifiable_log vspec) (i: nat{i <= length tl})
  : tl': verifiable_log vspec {length tl' = i}
  = prefix_base tl i

(* the verifier state after processing i entries *)
let state_pre #vspec (tl: verifiable_log vspec) (i:nat{i <= length tl}) =
  (verify (prefix tl i))

let state_post #vspec (tl: verifiable_log vspec) (i:seq_index tl)
  = (verify (prefix tl (i+1)))

(* the state after processing i'th entry is obtained by applying the verify
 * step to the state before processing the i'th entry *)
val lemma_state_transition (#vspec:verifier_spec) (tl: verifiable_log vspec) (i: seq_index tl):
  Lemma (ensures (state_post tl i ==
                  verify_step (index tl i) (state_pre tl i)))
        [SMTPat (verify_step (index tl i) (state_pre tl i))]

let gen_seq (vspec: verifier_spec): gen_seq_spec = {
  seq_t = verifiable_log vspec;
  length;
  prefix
}

let idxfn_t (vspec: verifier_spec) (b: eqtype) = IF.idxfn_t (gen_seq vspec) b

let cond_idxfn_t #vspec (b:eqtype) (f:idxfn_t vspec bool)
  = IF.cond_idxfn_t b f

val clock (#vspec:_) : (idxfn_t vspec timestamp)

(* the epoch of the i'th entry *)
let epoch_of #vspec (tl: verifiable_log vspec) (i: seq_index tl)
  = let t = clock tl i in
    t.e

(* clock is monotonic *)
val lemma_clock_monotonic (#vspec:verifier_spec)
  (tl: verifiable_log vspec) (i:nat) (j: seq_index tl {j >= i}):
  Lemma (ensures (clock tl i `ts_leq` clock tl j))

(* the thread id in the state is always the one specified in the parameter *)
val lemma_thread_id_state (#vspec:verifier_spec) (tl: verifiable_log vspec):
  Lemma (ensures (let tid, _ = tl in
                  vspec.tid (verify tl) = tid))

val is_blum_add (#vspec:_) (ep: epoch): idxfn_t vspec bool

val blum_add_elem (#vspec:_) (#ep: epoch):
  cond_idxfn_t #vspec (ms_hashfn_dom vspec.app) (is_blum_add ep)

val is_blum_evict (#vspec:_) (ep: epoch): idxfn_t vspec bool

val blum_evict_elem (#vspec:_) (#ep: epoch):
  cond_idxfn_t #vspec (ms_hashfn_dom vspec.app) (is_blum_evict ep)

(* is the i'th entry an app function *)
val is_appfn (#vspec:_): idxfn_t vspec bool

(* is the i'th entry within epoch ep *)
let is_within_epoch #vspec (ep: epoch)
  (tl: verifiable_log vspec) (i: seq_index tl)
  = epoch_of tl i <= ep

open Zeta.AppSimulate

(* for an appfn entry, return the function call params and result *)
val appfn_call_res (#vspec:_) (ep: epoch):
  cond_idxfn_t #vspec (appfn_call_res vspec.app) (conj is_appfn (is_within_epoch ep))
