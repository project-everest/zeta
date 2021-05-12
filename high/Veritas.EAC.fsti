module Veritas.EAC

open FStar.Seq
open Veritas.Key
open Veritas.MultiSetHash
open Veritas.Record
open Veritas.SeqAux
open Veritas.SeqMachine
open Veritas.State
open Veritas.Verifier

module V = Veritas.Verifier

let evict_vlog_entry = e:vlog_entry {is_evict e}
let nevict_vlog_entry = e:vlog_entry {not (is_evict e)}

type vlog_entry_ext =
  | NEvict: e:vlog_entry{not (is_evict e)} -> vlog_entry_ext
  | EvictMerkle: e:vlog_entry{is_evict_to_merkle e} -> v:value -> vlog_entry_ext
  | EvictBlum: e:vlog_entry{is_evict_to_blum e} -> v:value -> tid:nat -> vlog_entry_ext

let vlog_ext = seq (vlog_entry_ext)

type eac_state =
  | EACFail: eac_state
  | EACInit: eac_state
  | EACInStore: m:add_method -> v:value -> eac_state
  | EACEvictedMerkle: v:value -> eac_state
  | EACEvictedBlum: v:value -> t:timestamp -> j:nat -> eac_state
  | EACRoot: eac_state

let is_eac_state_evicted (s: eac_state): bool =
  match s with
  | EACEvictedMerkle _ -> true
  | EACEvictedBlum _ _ _ -> true
  | _ -> false

let is_eac_state_instore (s: eac_state): bool =
  match s with
  | EACInStore _ _ -> true
  | _ -> false

let eac_add (e: vlog_entry_ext) (s: eac_state) : eac_state =
  match s with
  | EACFail -> EACFail
  | EACInit -> (
    match e with
    | NEvict (AddM (k,v) _) -> if v = init_value k then EACInStore MAdd v
                               else EACFail
    | NEvict NextEpoch -> EACRoot
    | NEvict VerifyEpoch -> EACRoot
    | _ -> EACFail
    )

  | EACInStore m v -> (
    match e with
    | NEvict (Get _ v') -> if (DVal v') = v then s
                           else EACFail
    | NEvict (Put _ v') -> if (DVal? v) then EACInStore m (DVal v')
                           else EACFail
    | EvictMerkle (EvictM _ _) v' -> if DVal? v && v' <> v then EACFail
                                     else if MVal? v && not (MVal? v') then EACFail
                                     else EACEvictedMerkle v'
    | EvictBlum (EvictBM k k' t) v' j -> if DVal? v && v' <> v || m <> MAdd then EACFail
                                         else if MVal? v && not (MVal? v') then EACFail
                                         else EACEvictedBlum v' t j
    | EvictBlum (EvictB _ t) v' j ->  if DVal? v && v' <> v || m <> BAdd then EACFail
                                      else if MVal? v && not (MVal? v') then EACFail
                                      else EACEvictedBlum v' t j
    | _ -> EACFail
    )

  | EACEvictedMerkle v -> (
    match e with
    | NEvict (AddM (_,v') _) -> if v' = v then EACInStore MAdd v
                                else EACFail
    | _ -> EACFail
  )

  | EACEvictedBlum v t tid -> (
    match e with
    | NEvict (AddB (_,v') t' tid') -> if v' = v && t' = t && tid' = tid then EACInStore BAdd v
                                else EACFail
    | _ -> EACFail
  )

  | EACRoot -> (
    match e with
    | NEvict NextEpoch -> EACRoot
    | NEvict VerifyEpoch -> EACRoot
    | _ -> EACFail
  )

let eac_smk = SeqMachine EACInit EACFail eac_add

let to_vlog_entry (ee:vlog_entry_ext): vlog_entry =
  match ee with
  | EvictMerkle e _ -> e
  | EvictBlum e _ _ -> e
  | NEvict e -> e

let vlog_entry_ext_key (e: vlog_entry_ext): key =
  V.key_of (to_vlog_entry e)

let eac_sm = PSM eac_smk vlog_entry_ext_key

(* evict add consistency *)
let eac (l:vlog_ext) = valid_all eac_sm l

(* refinement of evict add consistent logs *)
type eac_log = l:vlog_ext{eac l}

let is_eac_log (l:vlog_ext): (r:bool{r <==> eac l}) =
  valid_all_comp eac_sm l

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
