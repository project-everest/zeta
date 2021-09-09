module Zeta.High.Interleave

open FStar.Seq
open Zeta.App
open Zeta.Key
open Zeta.GenKey
open Zeta.Record
open Zeta.Generic.Interleave
open Zeta.High.Verifier
open Zeta.EAC

module V = Zeta.GenericVerifier
module T = Zeta.Generic.Thread
module G = Zeta.Generic.Global
module GI = Zeta.Generic.Interleave
module HV = Zeta.High.Verifier
module I = Zeta.Interleave
module S = FStar.Seq
module SA = Zeta.SeqAux
module IF = Zeta.IdxFn
module SF = Zeta.SIdxFn
module EAC=Zeta.EAC

let ilog (app: app_params) = Zeta.Generic.Interleave.ilog (high_verifier_spec app)

let gen_seq (app: app_params)
  = Zeta.Generic.Interleave.gen_seq (high_verifier_spec app)

let verifiable_log (app:_) (n:nat)
  = il:ilog app n {verifiable il}

let thread_store (#app #n:_) (tid: nat{tid < n}) (il: verifiable_log app n)
  = let vs = thread_state tid il in
    vs.st

let has_some_add_of_key (#app #n:_) (bk: base_key) (il: verifiable_log app n)
  = exists i. HV.is_add_of_key bk (I.index il i)

let exists_in_some_store (#app #n:_) (bk: base_key)  (il: verifiable_log app n)
  = exists tid. store_contains (thread_store tid il) bk

val mk_vlog_entry_ext (#app: app_params) (#n:nat)
  : IF.idxfn_t (gen_seq app n) (vlog_entry_ext app)

val vlog_entry_ext_prop (#app #n:_) (il: verifiable_log app n) (i: seq_index il)
  : Lemma (ensures (let ee = mk_vlog_entry_ext il i in
                    let e = I.index il i in
                    e = to_vlog_entry ee))
          [SMTPat (mk_vlog_entry_ext il i)]

let vlog_ext_of_il_log (#app: app_params) (#n:nat)
  (il: verifiable_log app n)
  : seq (vlog_entry_ext app)
  = IF.map mk_vlog_entry_ext il

val is_eac (#app #n:_) (il: verifiable_log app n)
  : b:bool{b <==> eac (vlog_ext_of_il_log il)}

(* state after processing the i'th element *)
val eac_state_of_key (#app #n:_) (k: base_key)
  : IF.seqfn_t (gen_seq app n) (eac_state app k)

let eac_state_of_gkey (#app #n:_) (gk: key app) (il: verifiable_log app n)
  : (eac_state app (to_base_key gk))
  = let bk = to_base_key gk in
    eac_state_of_key bk il

(* is the key k in evicted state in *)
let is_eac_state_evicted (#app #n:_) (k: base_key) (il: verifiable_log app n): bool
  = EACEvictedMerkle? (eac_state_of_key k il) ||
    EACEvictedBlum? (eac_state_of_key k il)

let is_eac_state_active (#app #n:_) (k: base_key) (il: verifiable_log app n)
  = let es = eac_state_of_key k il in
    es <> EACInit && es <> EACFail

let is_eac_state_active_gk (#app #n:_) (gk: key app) (il: verifiable_log app n)
  = let es = eac_state_of_gkey gk il in
    es <> EACInit && es <> EACFail

val empty_implies_eac (#app #n:_) (il: verifiable_log app n)
  : Lemma (ensures (length il = 0 ==> is_eac il))

val eac_state_transition (#app #n:_) (k: base_key)
  (il: verifiable_log app n) (i: seq_index il)
  : Lemma (ensures (let es_pre = IF.to_pre_fn (eac_state_of_key k) il i in
                    let es_post = IF.to_post_fn (eac_state_of_key k) il i in
                    let smk = eac_smk app k in
                    let ee = mk_vlog_entry_ext il i in
                    es_post = eac_add ee es_pre))

let eac_log (app: app_params) (n:nat) = il: verifiable_log app n {is_eac il}

let neac_log (app: app_params) (n:nat) = il: verifiable_log app n {not (is_eac il)}

val lemma_eac_implies_prefix_eac (#app #n:_) (il: verifiable_log app n) (i: nat{i <= S.length il})
  : Lemma (ensures (is_eac il ==> is_eac (prefix il i)))
          [SMTPat (prefix il i)]

val lemma_eac_implies_appfn_calls_seq_consistent (#app #n:_) (il: eac_log app n)
  : Lemma (ensures (let gl = to_glog il in
                    Zeta.AppSimulate.seq_consistent (G.appfn_calls gl)))

val eac_implies_eac_state_valid (#app #n:_) (k: base_key)
  (il: verifiable_log app n)
  : Lemma (ensures (is_eac il ==> eac_state_of_key k il <> EACFail))

val eac_state_of_root_init (#app #n:_) (il: eac_log app n)
  : Lemma (ensures (eac_state_of_key Zeta.BinTree.Root il = EACInit))

val eac_state_active_implies_prev_add (#app #n:_) (k: base_key) (il: eac_log app n)
  : Lemma (ensures (is_eac_state_active k il <==> has_some_add_of_key k il))

(* when the eac_state of k is instore, then k is in the store of a unique verifier thread *)
val stored_tid (#app:_) (#n:nat) (k: base_key) (il: eac_log app n {EACInStore? (eac_state_of_key k il)})
  : tid:nat{tid < n /\ store_contains (thread_store tid il) k}

val lemma_instore (#app #n:_) (bk: base_key) (il: eac_log app n)
  : Lemma (ensures (exists_in_some_store bk il <==> EACInStore? (eac_state_of_key bk il)))

(* uniqueness: k is never in two stores *)
val key_in_unique_store (#app #n:_) (k:base_key) (il: eac_log app n) (tid1 tid2: thread_id il)
  : Lemma (ensures (tid1 <> tid2 ==>
                    ~ (store_contains (thread_store tid1 il) k /\ store_contains (thread_store tid2 il) k)))

val to_gen_key (#app #n:_) (bk: base_key) (il: eac_log app n {is_eac_state_active bk il})
  : gk:key app {to_base_key gk = bk}

val stored_key_is_correct (#app #n:_) (bk: base_key) (il: eac_log app n{EACInStore? (eac_state_of_key bk il)})
  : Lemma (ensures (let tid = stored_tid bk il in
                    let st = thread_store tid il in
                    stored_key st bk = to_gen_key bk il))

let stored_value (#app #n:_) (gk: key app) (il: eac_log app n{EACInStore? (eac_state_of_gkey gk il)})
  : value_t gk
  = let bk = to_base_key gk in
    let tid = stored_tid bk il in
    let st = thread_store tid il in
    stored_value st bk

let stored_add_method (#app #n:_) (gk: key app) (il: eac_log app n{EACInStore? (eac_state_of_gkey gk il)})
  : add_method
  = let bk = to_base_key gk in
    let tid = stored_tid bk il in
    let st = thread_store tid il in
    add_method_of st bk

(* the root is always in thread 0 *)
val lemma_root_in_store0 (#app #n:_) (il: eac_log app n)
  : Lemma (requires (n > 0))
          (ensures (store_contains (thread_store 0 il) Zeta.BinTree.Root))

val lemma_root_not_in_store (#app #n:_) (tid: nat{tid < n /\ tid > 0}) (il: eac_log app n)
  : Lemma (not (store_contains (thread_store tid il) Zeta.BinTree.Root))

val eac_value (#app #n:_) (k: key app) (il: eac_log app n)
  : value_t k

val eac_boundary (#app #n:_) (il: neac_log app n)
  : (i: seq_index il{is_eac (prefix il i) /\
                     ~ (is_eac (prefix il (i+1)))})

(* it can never happen that the verifier succeeds but eac fails in an app log entry *)
val eac_boundary_not_appfn (#app #n:_) (il: neac_log app n)
  : Lemma (ensures (let i = eac_boundary il in
                    let e = I.index il i in
                    not (V.is_appfn e)))

val eac_fail_key (#app #n:_) (il: neac_log app n)
  : k:base_key {let i = eac_boundary il in
                IF.to_post_fn (eac_state_of_key k) il i = EACFail /\
                IF.to_pre_fn (eac_state_of_key k) il i <> EACFail}

