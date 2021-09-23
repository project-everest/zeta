module Zeta.High.Interleave

open FStar.Seq
open Zeta.Interleave
open Zeta.App
open Zeta.Key
open Zeta.GenKey
open Zeta.Record
open Zeta.GenericVerifier
open Zeta.High.Verifier
open Zeta.EAC
open Zeta.Generic.Interleave

module V = Zeta.GenericVerifier
module T = Zeta.Generic.Thread
module G = Zeta.Generic.Global
module GI = Zeta.Generic.Interleave
module HV = Zeta.High.Verifier
module I = Zeta.Interleave
module S = FStar.Seq
module SA = Zeta.SeqAux
module EAC=Zeta.EAC
module MSD = Zeta.MultiSetHashDomain

let ilog (app: app_params) = Zeta.Generic.Interleave.ilog (high_verifier_spec app)

let verifiable_log (app:_) (n:nat)
  = il:ilog app n {verifiable il}

let thread_store (#app #n:_) (tid: nat{tid < n}) (il: verifiable_log app n)
  = let vs = thread_state tid il in
    vs.st

let thread_store_pre (#app #n:_) (tid: nat{tid < n}) (il: verifiable_log app n) (i: seq_index il)
  = let vs = thread_state_pre tid il i in
    vs.st

let thread_store_post (#app #n:_) (tid: nat{tid < n}) (il: verifiable_log app n) (i: seq_index il)
  = let vs = thread_state_post tid il i in
    vs.st

val runapp_refs_only_leafkeys (#app #n:_) (il: verifiable_log app n) (i:_ {RunApp? (index il i)}) (k: base_key)
  : Lemma (ensures (let e = index il i in
                    e `refs_key` k ==> is_leaf_key k))

val not_refs_implies_store_unchanged  (#app #n:_) (k:base_key) (t:nat{t < n})
  (il: verifiable_log app n) (i:seq_index il)
  : Lemma (ensures (let e = I.index il i in
                    let st_pre = thread_store_pre t il i in
                    let st_post = thread_store_post t il i in
                    not (e `exp_refs_key` k) ==>
                    store_contains st_pre k ==>
                    (store_contains st_post k /\
                     stored_key st_post k == stored_key st_pre k /\
                     stored_value st_post k == stored_value st_pre k)))

val runapp_doesnot_change_store_keys (#app #n:_) (k:base_key)
  (il: verifiable_log app n) (i: seq_index il {is_appfn il i})
  : Lemma (ensures (let t = src il i in
                    let st_pre = thread_store_pre t il i in
                    let st_post = thread_store_post t il i in
                    store_contains st_post k = store_contains st_pre k))

val blum_evict_elem_props
  (#app #n:_)
  (il: verifiable_log app n)
  (i: seq_index il {is_blum_evict il i})
  : Lemma (ensures (let e = I.index il i in
                    let MSD.MHDom (gk,vk) t_e tid_e = blum_evict_elem il i in
                    let tid = I.src il i in
                    let st_pre = thread_store_pre tid il i in
                    let k = V.evict_slot e in
                    k = to_base_key gk /\
                    store_contains st_pre k /\
                    gk = stored_key st_pre k /\
                    vk = stored_value st_pre k /\
                    t_e = V.blum_evict_timestamp e /\
                    tid_e = tid))
          [SMTPat (blum_evict_elem il i)]

let has_some_add_of_key (#app #n:_) (bk: base_key) (il: verifiable_log app n)
  = exists i. HV.is_add_of_key bk (I.index il i)

let has_some_ref_to_key (#app #n:_) (bk: base_key) (il: verifiable_log app n)
  = exists i. HV.refs_key (I.index il i) bk

let exists_in_some_store (#app #n:_) (bk: base_key)  (il: verifiable_log app n)
  = exists tid. store_contains (thread_store tid il) bk

val mk_vlog_entry_ext (#app: app_params) (#n:nat) (il: verifiable_log app n) (i: seq_index il)
  : vlog_entry_ext app

val vlog_entry_ext_prop (#app #n:_) (il: verifiable_log app n) (i: seq_index il)
  : Lemma (ensures (let ee = mk_vlog_entry_ext il i in
                    let e = I.index il i in
                    e = to_vlog_entry ee))
          [SMTPat (mk_vlog_entry_ext il i)]

val vlog_ext_of_il_log (#app: app_params) (#n:nat) (il: verifiable_log app n)
  : seq (vlog_entry_ext app)

val is_eac (#app #n:_) (il: verifiable_log app n)
  : b:bool{b <==> eac (vlog_ext_of_il_log il)}

(* state after processing the i'th element *)
val eac_state_of_key (#app #n:_) (k: base_key) (il: verifiable_log app n)
  : eac_state app k

let eac_state_of_key_pre (#app #n:_) (k: base_key) (il: verifiable_log app n) (i: seq_index il)
  = let il' = prefix il i in
    eac_state_of_key k il'

let eac_state_of_key_post (#app #n:_) (k: base_key) (il: verifiable_log app n) (i: seq_index il)
  = let il' = prefix il (i+1) in
    eac_state_of_key k il'

(* is the key k in evicted state in *)
let is_eac_state_evicted (#app #n:_) (k: base_key) (il: verifiable_log app n): bool
  = EACEvictedMerkle? (eac_state_of_key k il) ||
    EACEvictedBlum? (eac_state_of_key k il)

let is_eac_state_active (#app #n:_) (k: base_key) (il: verifiable_log app n)
  = let es = eac_state_of_key k il in
    es <> EACInit && es <> EACFail

let is_eac_state_instore (#app #n:_) (k:base_key) (il: verifiable_log app n)
  = let es = eac_state_of_key k il in
    let open Zeta.BinTree in
    k = Root && es = EACInit || EACInStore? es

let eac_state_of_genkey (#app #n:_) (gk: key app) (il: verifiable_log app n)
  : eac_state app (to_base_key gk)
  = let k = to_base_key gk in
    let es = eac_state_of_key k il in
    if EAC.is_eac_state_active es then
      if gk = to_gen_key es then es
      else EACInit
    else es

val empty_implies_eac (#app #n:_) (il: verifiable_log app n)
  : Lemma (ensures (length il = 0 ==> is_eac il))

val eac_state_empty (#app #n:_) (k: base_key)
  (il: verifiable_log app n{length il = 0})
  : Lemma (ensures (eac_state_of_key k il = EACInit))

val eac_state_snoc (#app #n:_) (k: base_key)
  (il: verifiable_log app n{length il > 0})
  : Lemma (ensures (let i = length il - 1  in
                    let il' = prefix il i in
                    let es' = eac_state_of_key k il' in
                    let es = eac_state_of_key k il in
                    let ee = mk_vlog_entry_ext il i in
                    es == eac_add ee es'))

val eac_state_transition (#app #n:_) (k: base_key)
  (il: verifiable_log app n) (i: seq_index il)
  : Lemma (ensures (let es_pre =  eac_state_of_key_pre k il i in
                    let es_post = eac_state_of_key_post k il i in
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
          [SMTPat (eac_state_of_key k il)]

val eac_state_of_root_init (#app #n:_) (il: eac_log app n)
  : Lemma (ensures (eac_state_of_key Zeta.BinTree.Root il = EACInit))

val eac_state_active_implies_prev_add (#app #n:_) (k: base_key) (il: eac_log app n)
  : Lemma (ensures (is_eac_state_active k il <==> has_some_add_of_key k il))

val eac_state_init_implies_no_key_refs (#app #n:_) (k: base_key) (il: eac_log app n)
  : Lemma (ensures (eac_state_of_key k il = EACInit ==> ~ (has_some_ref_to_key k il)))

(* when the eac_state of k is instore, then k is in the store of a unique verifier thread *)
val stored_tid (#app:_) (#n:nat) (k: base_key) (il: eac_log app n {is_eac_state_instore k il})
  : tid:nat{tid < n /\
          (let st = thread_store tid il in
           let es = eac_state_of_key k il in
           let gk = to_gen_key es in
           store_contains st k /\ gk = stored_key st k)}

val lemma_instore (#app #n:_) (bk: base_key) (il: eac_log app n)
  : Lemma (ensures (exists_in_some_store bk il <==> is_eac_state_instore bk il))

(* uniqueness: k is never in two stores *)
val key_in_unique_store (#app #n:_) (k:base_key) (il: eac_log app n) (tid1 tid2: thread_id il)
  : Lemma (ensures (tid1 <> tid2 ==>
                    ~ (store_contains (thread_store tid1 il) k /\ store_contains (thread_store tid2 il) k)))

let stored_value (#app #n:_)
  (gk: key app)
  (il: eac_log app n{let k = to_base_key gk in
                     let es = eac_state_of_key k il in
                     is_eac_state_instore k il /\
                     to_gen_key es = gk})
  : value_t gk
  = let bk = to_base_key gk in
    let tid = stored_tid bk il in
    let st = thread_store tid il in
    stored_value st bk

let stored_add_method (#app #n:_) (bk: base_key) (il: eac_log app n{EACInStore? (eac_state_of_key bk il)})
  : add_method
  = let tid = stored_tid bk il in
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

val eac_value_is_stored_value (#app #n:_) (il: eac_log app n) (gk: key app) (tid: nat {tid < n})
  : Lemma (requires (let bk = to_base_key gk in
                     store_contains (thread_store tid il) bk /\
                     stored_key (thread_store tid il) bk = gk))
          (ensures (let bk = to_base_key gk in
                    eac_value gk il = HV.stored_value (thread_store tid il) bk))

val eac_value_is_stored_value_int (#app #n:_) (il: eac_log app n) (k: merkle_key) (tid: nat{ tid < n })
  : Lemma (requires (store_contains (thread_store tid il) k))
          (ensures (eac_value (IntK k) il = HV.stored_value (thread_store tid il) k))

let eac_state_evicted_value (#app #bk:_) (es: eac_state app bk {EAC.is_eac_state_evicted es})
  : value app
  = match es with
    | EACEvictedBlum _ v _ _ -> v
    | EACEvictedMerkle _ v -> v

val eac_value_is_evicted_value (#app #n:_) (il: eac_log app n) (gk: key app):
  Lemma (requires (let bk = to_base_key gk in
                   let es = eac_state_of_key bk il in
                   is_eac_state_evicted bk il /\
                   gk = to_gen_key es))
        (ensures (let bk = to_base_key gk in
                  let es = eac_state_of_key bk il in
                  eac_state_evicted_value es = eac_value gk il))

val eac_value_init_state_is_init (#app #n:_) (il: eac_log app n) (gk: key app):
  Lemma (requires (let bk = to_base_key gk in
                   let es = eac_state_of_genkey gk il in
                   es = EACInit /\
                   bk <> Zeta.BinTree.Root))
        (ensures (eac_value gk il = init_value gk))

val eac_value_init
  (#app #n:_)
  (gk: key app)
  (il: eac_log app n {length il = 0})
  : Lemma (ensures (eac_value gk il = init_value gk))

let value_ext (#app:_) (ee: vlog_entry_ext app {EvictMerkle? ee \/ EvictBlum? ee})
  = match ee with
    | EvictMerkle _ v -> v
    | EvictBlum _ v _ -> v

val ext_evict_val_is_stored_val (#app #n:_) (il: verifiable_log app n) (i: seq_index il):
  Lemma (requires (V.is_evict (I.index il i)))
        (ensures (let tid = I.src il i in
                  let st_pre = thread_store_pre tid il i in
                  let e = I.index il i in
                  let ee = mk_vlog_entry_ext il i in
                  let bk = V.evict_slot e in
                  store_contains st_pre bk /\
                  HV.stored_value st_pre bk = value_ext ee))

val ext_blum_timestamp_is_src (#app #n:_) (il: verifiable_log app n) (i: seq_index il)
  : Lemma (requires (is_blum_evict il i))
          (ensures (let tid = I.src il i in
                    let EvictBlum _ _ tid_e = mk_vlog_entry_ext il i in
                    tid_e = tid))
          [SMTPat (blum_evict_elem il i)]

val ext_app_records_is_stored_val
  (#app #n:_)
  (il: verifiable_log app n)
  (i: seq_index il)
  : Lemma (requires (V.is_appfn (I.index il i)))
          (ensures (let open Zeta.GenericVerifier in
                    let App (RunApp f p ss) rs = mk_vlog_entry_ext il i in
                    let vs = cur_thread_state_pre il i in
                    Some? (get_record_set ss vs) /\
                    rs = get_record_set_succ ss vs))

val root_never_evicted (#app #n:_) (il: verifiable_log app n) (i: seq_index il)
  : Lemma (requires (V.is_evict (I.index il i)))
          (ensures (let e = I.index il i in
                    let bk = V.evict_slot e in
                    bk <> Zeta.BinTree.Root))

val root_never_added (#app #n:_) (il: verifiable_log app n) (i: seq_index il):
  Lemma (requires (V.is_add (I.index il i)))
        (ensures (let e = I.index il i in
                  let bk = V.add_slot e in
                  bk <> Zeta.BinTree.Root))

val eac_app_state_value_is_stored_value (#app #n:_) (il: eac_log app n) (gk: key app)
  : Lemma (requires (let bk = to_base_key gk in
                     let es = eac_state_of_genkey gk il in
                     AppK? gk /\ EACInStore? es))
          (ensures (let bk = to_base_key gk in
                    let EACInStore _ gk' v = eac_state_of_key bk il in
                    stored_value gk il = v))

(* for all keys, the add method stored in the store is the same as the add method associated
 * with eac state *)
val eac_add_method_is_stored_addm (#app #n:_) (il: eac_log app n) (bk: base_key)
  : Lemma (requires (EACInStore? (eac_state_of_key bk il)))
          (ensures (let EACInStore m _ _ = eac_state_of_key bk il in
                    m = stored_add_method bk il))

(* the state of each key for an empty log is init *)
val init_state_empty (#app #n:_) (il: verifiable_log app n {S.length il = 0}) (bk: base_key):
  Lemma (eac_state_of_key bk il = EACInit)

val eac_boundary (#app #n:_) (il: neac_log app n)
  : (i: seq_index il{is_eac (prefix il i) /\
                     ~ (is_eac (prefix il (i+1)))})

val eac_fail_key (#app #n:_) (il: neac_log app n)
  : k:base_key {let i = eac_boundary il in
                let e = I.index il i in
                eac_state_of_key_post k il i = EACFail /\
                eac_state_of_key_pre k il i <> EACFail /\
                e `refs_key` k}
