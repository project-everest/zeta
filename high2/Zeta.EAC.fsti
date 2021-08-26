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
  | App: e:vlog_entry app{is_appfn e} ->
         rs: appfn_rs_t (RunApp?.f e) { length rs = length (RunApp?.rs e) }   -> vlog_entry_ext app

let vlog_ext (app: app_params) = seq (vlog_entry_ext app)

type eac_state (app: app_params) (k: base_key) =
  | EACFail: eac_state app k
  | EACInit: eac_state app k
  | EACInStore: m:add_method -> v:value app -> eac_state app k
  | EACEvictedMerkle: v:value app -> eac_state app k
  | EACEvictedBlum: v:value app -> t:timestamp -> j:thread_id -> eac_state app k

let is_eac_state_evicted #app #k (s: eac_state app k): bool =
  match s with
  | EACEvictedMerkle _ -> true
  | EACEvictedBlum _ _ _ -> true
  | _ -> false

let is_eac_state_instore #app #k (s: eac_state app k): bool =
  match s with
  | EACInStore _ _ -> true
  | _ -> false

let refs_key #app (e: vlog_entry app) (k: base_key)
  = match e with
    | AddM _ k' _ -> k' = k
    | AddB _ k' _ _ -> k' = k
    | EvictM k' _ -> k' = k
    | EvictB k' _ -> k' = k
    | EvictBM k' _ _ -> k' = k
    | NextEpoch -> false
    | VerifyEpoch -> false
    | RunApp _ _ ks -> mem k ks

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
      | EACInStore m v ->
        let idx = index_mem ks refkeys in
        let (_,v') = index rs idx in
        if AppV v' <> v then EACFail
        else
          let v = AppV (index ws idx) in
          EACInStore m v
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
            if v = init_value k && to_base_key k = ks then EACInStore MAdd v
            else EACFail

          | NEvict NextEpoch ->
            s

          | NEvict VerifyEpoch ->
            s

          | _ ->
            EACFail
          )

        | EACInStore m v -> (
          match ee with

          | EvictMerkle (EvictM  _ _) v' ->
            if AppV? v && v' <> v then EACFail
            else if IntV? v && not (IntV? v') then EACFail
            else EACEvictedMerkle v'

          | EvictBlum (EvictBM k k' t) v' j ->
            if AppV? v && v' <> v || m <> MAdd then EACFail
            else if IntV? v && not (IntV? v') then EACFail
            else EACEvictedBlum v' t j

          | EvictBlum (EvictB _ t) v' j ->
            if AppV? v && v' <> v || m <> BAdd then EACFail
            else if IntV? v && not (IntV? v') then EACFail
            else EACEvictedBlum v' t j

          | _ ->
          EACFail
        )

        | EACEvictedMerkle v -> (
          match ee with
          | NEvict (AddM (_,v') _ _) ->
            if v' = v then EACInStore MAdd v
            else EACFail
          | _ -> EACFail
        )

        | EACEvictedBlum v t tid -> (
          match ee with
          | NEvict (AddB (_,v') _ t' tid') ->
            if v' = v && t' = t && tid' = tid then EACInStore BAdd v
            else EACFail
          | _ -> EACFail
        )

let eac_smk (app: app_params) (k: base_key) = SeqMachine EACInit EACFail (eac_add #app #k)

(* the eac state of a key after processing log l *)
let eac_state_of_key
  (#app: app_params)
  (k: key app)
  (l: vlog_ext app)
  : eac_state app (to_base_key k)
  = let open Zeta.SeqMachine in
    let bk = to_base_key k in
    seq_machine_run (eac_smk app bk) l

val eac_state_transition
  (#app: app_params)
  (k: key app)
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
  (k: key app)
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

(* computable version of eac *)
val is_eac_log (#app: app_params) (l:vlog_ext app): (r:bool{r <==> eac l})

val eac_value (#app: app_params) (k: key app) (l: eac_log app)
  : value_t k

let to_fncall (#app: app_params) (ee: vlog_entry_ext app {App? ee})
  = let App (RunApp fid_c arg_c _) inp_c = ee in
    {fid_c; arg_c; inp_c}

let appfn_call_seq
  (#app: app_params)
  (l: vlog_ext app)
  : seq (appfn_call app)
  = let open Zeta.SeqAux in
    let is_app = fun (i: seq_index l) ->
      App? (index l i)
    in
    let to_fncall = fun (i: seq_index l{is_app i}) ->
      let ee = index l i in
      to_fncall ee
    in
    indexed_filter_map l is_app to_fncall

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
