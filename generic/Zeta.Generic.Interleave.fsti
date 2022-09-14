module Zeta.Generic.Interleave

open FStar.Seq
open Zeta.SeqAux
open Zeta.Time
open Zeta.MultiSet
open Zeta.MultiSetHashDomain
open Zeta.AppSimulate
open Zeta.GenericVerifier
open Zeta.Generic.Thread
open Zeta.Generic.Global
open Zeta.Interleave

module V = Zeta.GenericVerifier
module T = Zeta.Generic.Thread
module G = Zeta.Generic.Global
module I = Zeta.Interleave
module S = FStar.Seq
module SA = Zeta.SeqAux

let ilog (vspec: verifier_spec) (n:nat) = interleaving (verifier_log_entry vspec) n

(* valid thread ids of an interleaving *)
let thread_id #vspec #n (il: ilog vspec n) = t:nat{t < n}

let seq_index #vspec #n (il: ilog vspec n) = SA.seq_index il

let length #vspec #n (il: ilog vspec n) = S.length il

let thread_state (#vspec: verifier_spec) (#n:_) (tid:nat{tid < n}) (il: ilog vspec n)
  = let gl = s_seq il in
    let tl = (tid, S.index gl tid) in
    T.state tl

let thread_state_pre (#vspec #n:_) (tid:nat{tid < n})
  (il: ilog vspec n) (i: seq_index il)
  = let il' = I.prefix il i in
    thread_state tid il'

let thread_state_post (#vspec #n:_) (tid:nat{tid < n})
  (il: ilog vspec n) (i: seq_index il)
  = let il' = I.prefix il (i+1) in
    thread_state tid il'

let cur_thread_state_pre (#vspec: verifier_spec) (#n:_) (il: ilog vspec n) (i: seq_index il)
  = let t = src il i in
    thread_state_pre t il i

let cur_thread_state_post (#vspec: verifier_spec) (#n:_) (il: ilog vspec n) (i: seq_index il)
  = let t = src il i in
    thread_state_post t il i

val lemma_cur_thread_state_extend (#vspec: verifier_spec) (#n:_)
  (il: ilog vspec n) (i: seq_index il)
  : Lemma (ensures (let st_pre = cur_thread_state_pre il i in
                    let st_post = cur_thread_state_post il i in
                    st_post == V.verify_step (I.index il i) st_pre))

val lemma_non_cur_thread_state_extend (#vspec: verifier_spec) (#n:_) (tid: nat{tid < n})
  (il: ilog vspec n) (i: seq_index il)
  : Lemma (requires (tid <> src il i))
          (ensures (let st_pre = thread_state_pre tid il i in
                    let st_post = thread_state_post tid il i in
                    st_pre == st_post))

(* an interleaving is verifiable is the source logs are verifiable *)
let verifiable #vspec #n (il: ilog vspec n) =
  G.verifiable (I.s_seq il)

let verifiable_log vspec n = il:ilog vspec n {verifiable il}

val lemma_prefix_verifiable (#vspec:_) (n:_) (il:verifiable_log vspec n) (i:nat{i <= S.length il}):
  Lemma (ensures (verifiable (I.prefix il i)))
        [SMTPat (I.prefix il i)]

(* to sequence of individual thread-level logs *)
let to_glog #vspec #n (il: verifiable_log vspec n): G.verifiable_log _
  = I.s_seq il

unfold
let prefix #vspec #n (il: verifiable_log vspec n) (i:nat{i <= S.length il})
  : il':verifiable_log vspec n {length il' = i}
  = I.prefix il i

val lemma_state_valid (#vspec:_) (n:_) (tid:nat{tid < n}) (il: verifiable_log vspec n)
  : Lemma (ensures (vspec.valid (thread_state tid il)))
          [SMTPat (thread_state tid il)]

val lemma_state_pre_valid (#vspec:_) (n:_) (tid:nat{tid < n}) (il: verifiable_log vspec n) (i: seq_index il)
  : Lemma (ensures (vspec.valid (thread_state_pre tid il i)))
          [SMTPat (thread_state_pre tid il i)]

val lemma_state_post_valid (#vspec:_) (n:_) (tid:nat{tid < n}) (il: verifiable_log vspec n) (i: seq_index il)
  : Lemma (ensures (vspec.valid (thread_state_post tid il i)))
          [SMTPat (thread_state_post tid il i)]

(* the clock value at every index *)
let clock (#vspec #n:_) (il: verifiable_log vspec n) (i: seq_index il)
  : GTot timestamp
  = let ti = i2s_map il i in
    G.clock (to_glog il) ti

val clock_prefix_prop (#vspec #n:_) (il: verifiable_log vspec n) (i: seq_index il) (j:nat{j <= length il /\ j > i})
  : Lemma (ensures (clock il i = clock (prefix il j) i))
          [SMTPat (clock (prefix il j) i)]

let epoch_of (#vspec #n:_) (il: verifiable_log vspec n) (i: seq_index il)
  : GTot epoch
  = let t = clock il i in
    t.e

let is_within_epoch (#vspec #n:_) (ep: epoch) (il: verifiable_log vspec n) (i: seq_index il)
  = epoch_of il i <= ep

let is_appfn (#vspec #n:_) (il: verifiable_log vspec n) (i: seq_index il)
  : bool
  = let ti = i2s_map il i in
    G.is_appfn (to_glog il) ti

let to_app_fcr (#vspec #n:_) (il: verifiable_log vspec n) (i: seq_index il{is_appfn il i})
  : GTot (appfn_call_res vspec.app)
  = let ti = i2s_map il i in
    G.to_app_fcr (to_glog il) ti


val lemma_thread_state_prefix (#vspec: verifier_spec) (#n:_)
  (il: verifiable_log vspec n) (i:seq_index il)
  : Lemma (ensures (let t,j = i2s_map il i in
                    let tl = G.index (to_glog il) t in
                    cur_thread_state_pre il i == T.state_pre tl j))
          [SMTPat (cur_thread_state_pre il i)]

let is_blum_add (#vspec #n:_) (il: verifiable_log vspec n) (i: seq_index il)
  : bool
  = let ti = i2s_map il i in
    G.is_blum_add (to_glog il) ti

val is_blum_add_prefix_prop
  (#vspec #n:_)
  (il: verifiable_log vspec n)
  (i: seq_index il)
  (j:nat{j <= length il /\ j > i})
  : Lemma (ensures (is_blum_add il i = is_blum_add (prefix il j) i))
          [SMTPat (is_blum_add (prefix il j) i)]

let blum_add_elem #vspec #n (il: verifiable_log vspec n) (i: seq_index il{is_blum_add il i})
  : ms_hashfn_dom vspec.app
  = let ti = i2s_map il i in
    G.blum_add_elem (to_glog il) ti

val blum_add_elem_prefix_prop
  (#vspec #n:_)
  (il: verifiable_log vspec n)
  (i: seq_index il{is_blum_add il i})
  (j:nat{j <= length il /\ j > i})
  : Lemma (ensures (blum_add_elem il i = blum_add_elem (prefix il j) i))
          [SMTPat (blum_add_elem (prefix il j) i)]

let is_blum_evict  (#vspec #n:_) (il: verifiable_log vspec n) (i: seq_index il)
  : bool
  = let ti = i2s_map il i in
    G.is_blum_evict (to_glog il) ti

let blum_evict_elem #vspec #n (il: verifiable_log vspec n) (i: seq_index il{is_blum_evict il i})
  : GTot (ms_hashfn_dom vspec.app)
  = let ti = i2s_map il i in
    G.blum_evict_elem (to_glog il) ti

val blum_evict_elem_prefix_prop
  (#vspec #n:_)
  (il: verifiable_log vspec n)
  (i: seq_index il{is_blum_evict il i})
  (j:nat{j <= length il /\ j > i})
  : Lemma (ensures (blum_evict_elem il i = blum_evict_elem (prefix il j) i))
          [SMTPat (blum_evict_elem (prefix il j) i)]

val app_fcrs_il (#vspec: verifier_spec) (#n:_) (il: verifiable_log vspec n)
  : GTot (interleaving (Zeta.AppSimulate.appfn_call_res vspec.app) n)

let app_fcrs (#vspec: verifier_spec) (#n:_) (il: verifiable_log vspec n)
  : GTot (seq (Zeta.AppSimulate.appfn_call_res vspec.app))
  = i_seq (app_fcrs_il il)

val lemma_app_fcrs_interleave (#app #n:_) (il: verifiable_log app n)
  : Lemma (ensures (let fcrs_il = app_fcrs_il il in
                    let gl = to_glog il in
                    s_seq fcrs_il = G.app_fcrs gl))
          [SMTPat (app_fcrs_il il)]

val app_fcrs_empty (#app #n:_) (il: verifiable_log app n)
  : Lemma (ensures (length il = 0 ==> S.length (app_fcrs il) = 0))

val appfn_calls_snoc (#app #n:_) (il: verifiable_log app n {length il > 0})
  : Lemma (ensures (let i = length il - 1 in
                    let e = index il i in
                    let il' = prefix il i in
                    let cr = app_fcrs il in
                    let cr' = app_fcrs il' in
                    match e with
                    | RunApp _ _ _ -> cr == SA.append1 cr' (to_app_fcr il i)
                    | _ -> cr == cr'))
