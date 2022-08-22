module Zeta.KeyValueStore.Spec

open Zeta.App

type u8 = FStar.UInt8.t

let vget_id : u8 = 0uy
let vput_id : u8 = 1uy

assume val key_t : eqtype
assume val value_t : eqtype

let adm : app_data_model = AppDataModel key_t value_t

let vget_arg_t : code = TPair TKey TValue
let vget_res_t : code = TUnit
let vget_arity : nat = 1
let vget_f : app_fn_t adm vget_arg_t vget_res_t vget_arity =
  fun (k_arg, v_arg) inp ->
  let k_store, v_store = Seq.index inp 0 in
  if k_arg = k_store && DValue v_arg = v_store
  then Fn_success, (), Seq.create 1 v_store
  else Fn_failure, (), Seq.create 1 v_store
let vget_sig : fn_sig adm = {
  farg_t = vget_arg_t;
  fres_t = vget_res_t;
  arity = vget_arity;
  f = vget_f
}

let vput_arg_t : code = TPair TKey TValue
let vput_res_t : code = TUnit
let vput_arity : nat = 1
let vput_f : app_fn_t adm vput_arg_t vput_res_t vput_arity =
  fun (k_arg, v_arg) inp ->
  let k_store, v_store = Seq.index inp 0 in
  if k_arg = k_store
  then Fn_success, (), Seq.create 1 (DValue v_arg)
  else Fn_success, (), Seq.create 1 v_store
let vput_sig : fn_sig adm = {
  farg_t = vput_arg_t;
  fres_t = vput_res_t;
  arity = vput_arity;
  f = vput_f
}

let kv_fn_tbl : fn_tbl adm =
  Map.restrict (Set.union (Set.singleton vget_id)
                          (Set.singleton vput_id))
               (Map.map_literal (fun id -> if id = vget_id
                                 then vget_sig
                                 else vput_sig))
