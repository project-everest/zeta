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

(* is the key k in evicted state in *)
let is_eac_state_evicted (#app #n:_) (k: base_key) (il: verifiable_log app n): bool
  = EACEvictedMerkle? (eac_state_of_key k il) ||
    EACEvictedBlum? (eac_state_of_key k il)

val eac_value (#app #n:_) (gk: key app)
  : IF.seqfn_t (gen_seq app n) (value_t gk)

val empty_implies_eac (#app #n:_) (il: verifiable_log app n)
  : Lemma (ensures (length il = 0 ==> is_eac il))

val eac_state_transition (#app #n:_) (k: base_key)
  (il: verifiable_log app n) (i: seq_index il)
  : Lemma (ensures (let es_pre = IF.to_pre_fn (eac_state_of_key k) il i in
                    let es_post = IF.to_post_fn (eac_state_of_key k) il i in
                    let smk = eac_smk app k in
                    let ee = mk_vlog_entry_ext il i in
                    es_post = eac_add ee es_pre))

val eac_implies_eac_state_valid (#app #n:_) (k: base_key)
  (il: verifiable_log app n)
  : Lemma (ensures (is_eac il ==> eac_state_of_key k il <> EACFail))

val eac_state_of_root_init (#app #n:_) (il: verifiable_log app n)
  : Lemma (ensures (eac_state_of_key Zeta.BinTree.Root il = EACInit))

let eac_log (app: app_params) (n:nat) = il: verifiable_log app n {is_eac il}

let neac_log (app: app_params) (n:nat) = il: verifiable_log app n {not (is_eac il)}

val lemma_eac_implies_prefix_eac (#app #n:_) (il: verifiable_log app n) (i: nat{i <= S.length il})
  : Lemma (ensures (is_eac il ==> is_eac (prefix il i)))
          [SMTPat (prefix il i)]

val lemma_eac_implies_appfn_calls_seq_consistent (#app #n:_) (il: eac_log app n)
  : Lemma (ensures (let gl = to_glog il in
                    Zeta.AppSimulate.seq_consistent (G.appfn_calls gl)))


val eac_boundary (#app #n:_) (il: neac_log app n)
  : (i: seq_index il{is_eac (prefix il i) /\
                     ~ (is_eac (prefix il (i+1)))})

(* it can never happen that the verifier succeeds but eac fails in an app log entry *)
val eac_boundary_not_appfn (#app #n:_) (il: neac_log app n)
  : Lemma (ensures (let i = eac_boundary il in
                    let e = I.index il i in
                    not (V.is_appfn e)))

