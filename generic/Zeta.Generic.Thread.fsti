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

(* the type of functions that return a value at position i *)
let idxfn_t_base (vspec: verifier_spec) (b: eqtype)
  = (tl: verifiable_log vspec -> i: seq_index tl -> b)

(* prefix property means that the value of function i depends only on the prefix until i *)
let prefix_property #vspec #b (f: idxfn_t_base vspec b)
  = forall (tl: verifiable_log vspec) (i: nat) (j:nat).
      {:pattern f (prefix tl j) i}
      j <= length tl ==>
      i < j ==>
      f tl i = f (prefix tl j) i

let idxfn_t (vspec: verifier_spec) (b: eqtype) = f:(idxfn_t_base vspec b){prefix_property f}

(* conjunction of two index filters *)
let conj #vspec (f1 f2: idxfn_t vspec bool)
  = fun (tl: verifiable_log vspec) (i: seq_index tl) ->
      f1 tl i && f2 tl i

val conj_is_idxfn (#vspec:_) (f1 f2: idxfn_t vspec bool)
  : Lemma (ensures (prefix_property (conj f1 f2)))
          [SMTPat (conj f1 f2)]

(* the type of functions that return a value at position i, but defined only for positions satisfying a filter *)
let cond_idxfn_t_base #vspec (b:eqtype) (f: idxfn_t vspec bool)
  = tl:verifiable_log vspec -> i: seq_index tl {f tl i} -> b

let cond_prefix_property #vspec #b (#f: idxfn_t vspec bool) (m: cond_idxfn_t_base b f)
  = forall (tl: verifiable_log vspec) (i:nat) (j:nat).
      {:pattern m (prefix tl j) i}
      j <= length tl ==>
      i < j ==>
      f tl i ==>
      m tl i = m (prefix tl j) i

let cond_idxfn_t #vspec (b:eqtype) (f:idxfn_t vspec bool)
  = m:(cond_idxfn_t_base b f){cond_prefix_property m}

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

noeq
type fm_t (vspec:_) (b:eqtype) =
  | FM: f: idxfn_t vspec bool ->
        m: cond_idxfn_t b f -> fm_t vspec b

let to_fm #vspec #b (#f: idxfn_t vspec bool) (m: cond_idxfn_t b f)
  = FM f m

(* filter each element of the log using fm.f and map them using fm.m *)
val filter_map (#vspec:_) (#b:_)
  (fm: fm_t vspec b)
  (tl: verifiable_log vspec)
  : S.seq b

(* map an index of the original sequence to the filter-mapped sequence *)
val filter_map_map (#vspec:_) (#b:_)
  (fm: fm_t vspec b)
  (tl: verifiable_log vspec)
  (i: seq_index tl {fm.f tl i})
  : j: (SA.seq_index (filter_map fm tl)) {S.index (filter_map fm tl) j == fm.m tl i}

(* map an index of the filter-map back to the original sequence *)
val filter_map_invmap (#vspec:_) (#b:_)
  (fm: fm_t vspec b)
  (tl: verifiable_log vspec)
  (j: SA.seq_index (filter_map fm tl))
  : i:(seq_index tl){fm.f tl i /\ filter_map_map fm tl i = j }

(* the above two index mappings are inverses of one-another *)
val lemma_filter_map (#vspec:_) (#b:_)
  (fm: fm_t vspec b)
  (tl: verifiable_log vspec)
  (i: seq_index tl {fm.f tl i})
  : Lemma (ensures (let j = filter_map_map fm tl i in
                    i = filter_map_invmap fm tl j))
          [SMTPat (filter_map_map fm tl i)]

val lemma_filter_map_extend_sat
  (#vspec:_)
  (#b:eqtype)
  (fm: fm_t vspec b)
  (tl: verifiable_log vspec {length tl > 0 /\ fm.f tl (length tl - 1)})
  : Lemma (ensures (let fms = filter_map fm tl in
                    let fms' = filter_map fm (prefix tl (length tl - 1)) in
                    let me = fm.m tl (length tl - 1) in
                    fms == SA.append1 fms' me))
          [SMTPat (filter_map fm tl)]

val lemma_filter_map_extend_unsat
  (#vspec:_)
  (#b:eqtype)
  (fm: fm_t vspec b)
  (tl: verifiable_log vspec {length tl > 0 /\ not (fm.f tl (length tl - 1))})
  : Lemma (ensures (let fms = filter_map fm tl in
                    let fms' = filter_map fm (prefix tl (length tl - 1)) in
                    fms == fms'))
          [SMTPat (filter_map fm tl)]

val lemma_filter_map_empty
  (#vspec:_)
  (#b:eqtype)
  (fm: fm_t vspec b)
  (tl: verifiable_log vspec {length tl = 0})
  : Lemma (ensures S.length (filter_map fm tl) = 0)
          [SMTPat (filter_map fm tl)]
