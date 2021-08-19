module Zeta.EAC

open FStar.Seq
open Zeta.SeqMachine
open Zeta.Time
open Zeta.Key
open Zeta.App
open Zeta.AppSimulate
open Zeta.Record
open Zeta.GenericVerifier
open Zeta.High.Verifier

let evict_vlog_entry (app: app_params) = e:(vlog_entry app) {is_evict e}

let nevict_vlog_entry (app: app_params) = e:(vlog_entry app) {not (is_evict e)}

type vlog_entry_ext (app: app_params) =
  | NEvict: e:vlog_entry app{is_internal e && not (is_evict e)} -> vlog_entry_ext app
  | EvictMerkle: e:vlog_entry app{is_merkle_evict e} -> v:value app -> vlog_entry_ext app
  | EvictBlum: e:vlog_entry app{is_blum_evict e} -> v:value app -> tid:thread_id -> vlog_entry_ext app
  | App: e:vlog_entry app{is_appfn e} -> rs: seq (record app) -> vlog_entry_ext app

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

let eac_add #app #ks (ee: vlog_entry_ext app) (s: eac_state app ks) : eac_state app ks
  = let e = to_vlog_entry ee in
    (* if this entry does not reference key ks, the state is unchanged *)
    if not (e `refs_key` ks) then s
    else
      match s with
      | EACFail ->
        EACFail

      | EACInit -> (
        match ee with

        | NEvict (AddM (k,v) _ _) ->
          if v = init_value k then EACInStore MAdd v
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
      | App (RunApp f p _) rs ->
        if length rs <> appfn_arity f then EACFail
        else
          EACFail

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

(* evict add consistency *)
let eac #app (l:vlog_ext app) =
  forall (k: base_key). {:pattern Zeta.SeqMachine.valid (eac_smk app k) l} Zeta.SeqMachine.valid (eac_smk app k) l

(* refinement of evict add consistent logs *)
let eac_log app = l:vlog_ext app{eac l}

(* computable version of eac *)
val is_eac_log (#app: app_params) (l:vlog_ext app): (r:bool{r <==> eac l})

let max_eac_prefix (l:vlog_ext{not (is_eac_log l)}):
  (i:nat{i < length l /\
        is_eac_log (prefix l i) /\
        not (is_eac_log (prefix l (i + 1)))}) =
  max_valid_all_prefix eac_sm l

(* the state operations of a vlog *)
let is_state_op (e: vlog_entry): bool =
  match e with
  | Get k v -> true
  | Put k v -> true
  | _ -> false

(* map vlog entry to state op *)
let to_state_op (e:vlog_entry {is_state_op e}): state_op =
  match e with
  | Get k v -> Veritas.State.Get k v
  | Put k v -> Veritas.State.Put k v

(* filter out the state ops of vlog *)
let to_state_op_vlog (l: vlog) =
  map to_state_op (filter_refine is_state_op l)

(* valid eac states *)
let is_eac_state_active (st:eac_state): bool = st <> EACFail &&
                                           st <> EACInit &&
                                           st <> EACRoot

let is_evict_ext (e:vlog_entry_ext): bool =
  match e with
  | EvictMerkle _ _ -> true
  | EvictBlum _ _ _ -> true
  | _ -> false

let value_ext (e:vlog_entry_ext{is_evict_ext e}): value =
  match e with
  | EvictMerkle _ v -> v
  | EvictBlum _ v _ -> v

(* value of a valid state *)
let value_of (st:eac_state {is_eac_state_active st}): value =
  match st with
  | EACInStore _ v -> v
  | EACEvictedMerkle v -> v
  | EACEvictedBlum v _ _ -> v

let add_method_of (st:eac_state {is_eac_state_instore st}): add_method =
  match st with
  | EACInStore m _ -> m

let to_vlog (l:vlog_ext) =
  map to_vlog_entry l

val lemma_eac_implies_rw_consistent (le:eac_log):
  Lemma (rw_consistent (to_state_op_vlog (to_vlog le)))

val is_eac (l:vlog_ext) : b:bool{b <==> eac l}
