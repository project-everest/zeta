module Zeta.KeyValueStore.Spec

open Zeta.App

module P = Zeta.Steel.Parser
module F = Zeta.KeyValueStore.Formats

/// Specification of the key value store app

type u8 = FStar.UInt8.t
type u16 = FStar.UInt16.t

let vget_id : u8 = 0uy
let vput_id : u8 = 1uy

let adm : app_data_model = AppDataModel F.key_t F.value_t

val key_hash_fn (k:F.key_t) : Zeta.Key.leaf_key
val key_cmp_fn : Zeta.MultiSet.cmp (app_key adm)

val value_hash_fn (v:app_value_nullable adm) : Zeta.Hash.hash_value
val value_cmp_fn : Zeta.MultiSet.cmp (app_value_nullable adm)

let vget_spec_arg_t : code = TPair TKey TValue
let vget_spec_res_t : code = TUnit
let vget_spec_arity : nat = 1
let vget_spec_f : app_fn_t adm vget_spec_arg_t vget_spec_res_t vget_spec_arity =
  fun (k_arg, v_arg) inp ->
  let k_store, v_store = Seq.index inp 0 in
  if k_arg = k_store && DValue v_arg = v_store
  then Fn_success, (), Seq.create 1 v_store
  else Fn_failure, (), Seq.create 1 v_store
let vget_sig : fn_sig adm = {
  farg_t = vget_spec_arg_t;
  fres_t = vget_spec_res_t;
  arity = vget_spec_arity;
  writes_output_log = false;
  f = vget_spec_f
}

let vput_spec_arg_t : code = TPair TKey TValue
let vput_spec_res_t : code = TUnit
let vput_spec_arity : nat = 1
let vput_spec_f : app_fn_t adm vput_spec_arg_t vput_spec_res_t vput_spec_arity =
  fun (k_arg, v_arg) inp ->
  let k_store, v_store = Seq.index inp 0 in
  if k_arg = k_store
  then Fn_success, (), Seq.create 1 (DValue v_arg)
  else Fn_failure, (), Seq.create 1 v_store
let vput_sig : fn_sig adm = {
  farg_t = vput_spec_arg_t;
  fres_t = vput_spec_res_t;
  arity = vput_spec_arity;
  writes_output_log = false;
  f = vput_spec_f
}

let kv_fn_tbl : fn_tbl adm =
  Map.restrict (Set.union (Set.singleton vget_id)
                          (Set.singleton vput_id))
               (Map.map_literal (fun id -> if id = vget_id
                                 then vget_sig
                                 else vput_sig))

let kv_params : app_params = {
  adm = adm;
  tbl = kv_fn_tbl;
  keyhashfn = key_hash_fn;
  valuehashfn = value_hash_fn;
  keycmp = key_cmp_fn;
  valcmp = value_cmp_fn;
}
