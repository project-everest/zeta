module Zeta.EAC

open FStar.Seq
open Zeta.SeqMachine
open Zeta.Time
open Zeta.Key
open Zeta.App
open Zeta.AppSimulate
open Zeta.GenKey
open Zeta.Record
open Zeta.GenericVerifier
open Zeta.High.Verifier

let evict_vlog_entry (app: app_params) = e:(vlog_entry app) {is_evict e}

let nevict_vlog_entry (app: app_params) = e:(vlog_entry app) {not (is_evict e)}

type vlog_entry_ext (app: app_params) =
  | NEvict: e:vlog_entry app{is_internal e && not (is_evict e)} -> vlog_entry_ext app
  | EvictMerkle: e:vlog_entry app{is_merkle_evict e} -> v:value app -> vlog_entry_ext app
  | EvictBlum: e:vlog_entry app{is_blum_evict e} -> v:value app -> tid:thread_id -> vlog_entry_ext app
  | App: e:vlog_entry app{is_appfn e /\ Zeta.SeqAux.distinct_elems (RunApp?.rs e)} ->
         rs: appfn_rs_t (RunApp?.f e) { length rs = length (RunApp?.rs e) }   -> vlog_entry_ext app

let vlog_ext (app: app_params) = seq (vlog_entry_ext app)

type eac_state (app: app_params) (k: base_key) =
  | EACFail: eac_state app k
  | EACInit: eac_state app k
  | EACInStore: m:add_method -> gk:key app {to_base_key gk = k} -> v:value_t gk -> eac_state app k
  | EACEvictedMerkle: gk:key app {to_base_key gk = k} -> v:value_t gk -> eac_state app k
  | EACEvictedBlum: gk: key app{to_base_key gk = k} -> v:value_t gk -> t:timestamp -> j:thread_id -> eac_state app k

let is_eac_state_evicted #app #k (s: eac_state app k): bool =
  match s with
  | EACEvictedMerkle _ _ -> true
  | EACEvictedBlum _ _ _ _ -> true
  | _ -> false

let is_eac_state_instore #app #k (s: eac_state app k): bool =
  match s with
  | EACInStore _ _ _ -> true
  | _ -> false

let to_vlog_entry #app (ee:vlog_entry_ext app): vlog_entry app =
  match ee with
  | EvictMerkle e _ -> e
  | EvictBlum e _ _ -> e
  | NEvict e -> e
  | App e _ -> e

(* implement eac_add for app entries *)
let eac_add_app #app #ks (ee: vlog_entry_ext app {App? ee}) (s: eac_state app ks)
  : eac_state app ks
  = let e = to_vlog_entry ee in
    let App (RunApp f p refkeys) rs = ee in
    let fn = appfn f in
    let rc,_,ws = fn p rs in

    (* any app failure leads to eac failure *)
    if rc = Fn_failure then EACFail
    (* propagate state if e does not ref the key we are tracking *)
    else if not (e `refs_key` ks) then s
    else
      match s with
      | EACInStore m gk v ->
        let idx = index_mem ks refkeys in
        let (gk',v') = index rs idx in
        if AppV v' <> v then EACFail
        else if AppK gk' <> gk then EACFail
        else
          let v = AppV (index ws idx) in
          EACInStore m gk v
      | _ -> EACFail

let eac_add #app #ks (ee: vlog_entry_ext app) (s: eac_state app ks) : eac_state app ks
  = if App? ee then eac_add_app ee s
    else
      let e = to_vlog_entry ee in
      (* if this entry does not reference key ks, the state is unchanged *)
      if not (e `refs_key` ks) then s
      else
        match s with
        | EACFail ->
          EACFail

        | EACInit -> (
          match ee with

          | NEvict (AddM (k,v) _ _) ->
            if v = init_value k && to_base_key k = ks then EACInStore MAdd k v
            else EACFail

          | NEvict NextEpoch ->
            s

          | NEvict VerifyEpoch ->
            s

          | _ ->
            EACFail
          )

        | EACInStore m k v -> (
          match ee with

          | EvictMerkle (EvictM  _ _) v' ->
            if AppV? v && v' <> v then EACFail
            else if IntV? v && not (IntV? v') then EACFail
            else EACEvictedMerkle k v'

          | EvictBlum (EvictBM _ k' t) v' j ->
            if AppV? v && v' <> v || m <> MAdd then EACFail
            else if IntV? v && not (IntV? v') then EACFail
            else EACEvictedBlum k v' t j

          | EvictBlum (EvictB _ t) v' j ->
            if AppV? v && v' <> v || m <> BAdd then EACFail
            else if IntV? v && not (IntV? v') then EACFail
            else EACEvictedBlum k v' t j

          | _ ->
          EACFail
        )

        | EACEvictedMerkle k v -> (
          match ee with
          | NEvict (AddM (k',v') _ _) ->
            if v' = v  && k' = k then EACInStore MAdd k v
            else EACFail
          | _ -> EACFail
        )

        | EACEvictedBlum k v t tid -> (
          match ee with
          | NEvict (AddB (k',v') _ t' tid') ->
            if k' = k && v' = v && t' = t && tid' = tid then EACInStore BAdd k v
            else EACFail
          | _ -> EACFail
        )

let eac_smk (app: app_params) (k: base_key) = SeqMachine EACInit EACFail (eac_add #app #k)

(* the eac state of a key after processing log l *)
let eac_state_of_key
  (#app: app_params)
  (k: base_key)
  (l: vlog_ext app)
  : eac_state app k
  = let open Zeta.SeqMachine in
    seq_machine_run (eac_smk app k) l

val empty_log_implies_init_state
  (#app: _)
  (k: base_key)
  (l: vlog_ext app{length l = 0})
  : Lemma (ensures (eac_state_of_key k l = EACInit))

val eac_state_transition
  (#app: app_params)
  (k: base_key)
  (l: vlog_ext app {length l > 0})
  : Lemma (ensures (let open Zeta.SeqAux in
                    let n = length l - 1 in
                    let l' = prefix l n in
                    let ee = index l n in
                    let es' = eac_state_of_key k l' in
                    let es = eac_state_of_key k l in
                    es = eac_add ee es'))
           [SMTPat (eac_state_of_key k l)]

(* evict add consistency *)
let eac #app (l:vlog_ext app) =
  forall (k: base_key). {:pattern Zeta.SeqMachine.valid (eac_smk app k) l} Zeta.SeqMachine.valid (eac_smk app k) l

(* refinement of evict add consistent logs *)
let eac_log app = l:vlog_ext app{eac l}

val eac_empty_log
  (#app: app_params)
  (l: vlog_ext app {length l = 0})
  : Lemma (ensures (eac l))

val eac_implies_prefix_eac
  (#app: app_params)
  (l: eac_log app)
  (i: nat {i <= length l})
  : Lemma (ensures (eac (Zeta.SeqAux.prefix l i)))
          [SMTPat (Zeta.SeqAux.prefix l i)]

val lemma_eac_state_of_key
  (#app: app_params)
  (l: eac_log app)
  (k: base_key)
  : Lemma (ensures (eac_state_of_key k l <> EACFail))
          [SMTPat (eac_state_of_key k l)]

val max_eac_prefix
  (#app: app_params)
  (l:vlog_ext app)
  : (i:nat{let open Zeta.SeqAux in
          eac l /\ i = length l
          \/
          i < length l /\
          eac (prefix l i) /\
          ~ (eac (prefix l (i + 1)))})

val eac_fail_key
  (#app: app_params)
  (l:vlog_ext app {~ (eac l)})
  : k:base_key {let open Zeta.SeqAux in
                let i = max_eac_prefix l in
                ~ (valid (eac_smk app k) (prefix l (i+1)))}

(* computable version of eac *)
val is_eac_log (#app: app_params) (l:vlog_ext app): (r:bool{r <==> eac l})

val eac_value (#app: app_params) (k: key app) (l: eac_log app)
  : value_t k

let to_fncall (#app: app_params) (ee: vlog_entry_ext app {App? ee})
  = let App (RunApp fid_c arg_c _) inp_c = ee in
    {fid_c; arg_c; inp_c}

val appfn_call_seq
  (#app: app_params)
  (le: vlog_ext app)
  : l:seq (appfn_call app){length le = length l}

let eac_app_state #app (l: eac_log app) (ak: app_key app.adm)
  = let gk = AppK ak in
    AppV?.v (eac_value gk l)

val eac_implies_valid_simulation (#app: app_params) (l: eac_log app)
  : Lemma (ensures (let fs = appfn_call_seq l in
                    Some? (simulate fs)))
          [SMTPat (eac l)]

val eac_state_is_app_state (#app: app_params) (l: eac_log app)
  : Lemma (ensures (let fs = appfn_call_seq l in
                    let app_state,_ = Some?.v (simulate fs) in
                    app_state == eac_app_state l))

let eac_add_method (#app: app_params) (#k: base_key) (es: eac_state app k {EACInStore? es})
  = let EACInStore m _ _ = es in
    m

let is_add_of_key #app (bk: base_key) (ee: vlog_entry_ext app)
  = let e = to_vlog_entry ee in
    is_add_of_key bk e

let has_some_add (#app: app_params) (bk: base_key) (le: vlog_ext app)
  : bool
  = let open Zeta.SeqAux in
    exists_sat_elems (is_add_of_key bk) le

let last_add_method (#app: app_params) (bk: base_key) (le: vlog_ext app {has_some_add bk le})
  : add_method
  = let open Zeta.SeqAux in
    let i = last_index (is_add_of_key bk) le in
    let ee = index le i in
    let e  = to_vlog_entry ee in
    add_method_of_entry e

let ee_refs_key (#app: app_params) (bk: base_key) (ee: vlog_entry_ext app)
  = let e = to_vlog_entry ee in
    e `refs_key` bk

let has_some_ref_to_key (#app:_) (bk: base_key) (le: vlog_ext app)
  : bool
  = let open Zeta.SeqAux in
    exists_sat_elems (ee_refs_key bk) le

val eac_instore_implies_equiv_some_add (#app: app_params) (bk: base_key) (le: eac_log app)
  : Lemma (ensures (let es = eac_state_of_key bk le in
                    let open Zeta.SeqAux in
                    (EACInStore? es ==> (has_some_add bk le /\
                                         eac_add_method es = last_add_method bk le))))

val eac_init_implies_no_keyrefs (#app:_) (bk: base_key) (le: eac_log app {eac_state_of_key bk le = EACInit})
  : Lemma (ensures (not (has_some_ref_to_key bk le)))
