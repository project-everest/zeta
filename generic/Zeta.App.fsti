module Zeta.App

open Zeta.Hash
open Zeta.Key

type u8 = FStar.UInt8.t
type u16 = FStar.UInt16.t
type u32 = FStar.UInt32.t
type u64 = FStar.UInt64.t

(*
 * We first define representation for the argument and result types of
 *   the functions that the verifier supports
 *
 * These are representations of the F* types,
 *   their interpretation is given by the interp_code function
 *
 * Note that we encode key and value also
 *   This allows us to pass around keys and values with other arguments,
 *   modeling multiple keys etc. using TPair
 *   For example, see below the representations for vget and vput (vget_sig and vput_sig)
 *
 *)

type code =
  | TUnit
  | TUInt8
  | TUInt16
  | TUInt32
  | TUInt64
  //| TKey
  | TValue
  | TPair : code -> code -> code

(*
 * the application data model specifies the codes for key and data.
 * Currently, the keys are hard-coded to 256 bit vectors.
 * TODO: Generalize this to arbitrary keys.
 *)
noeq type app_data_model =
  | AppDataModel: value: eqtype -> app_data_model

(* key type of the application *)
let app_key (adm: app_data_model) =  key

(* value type of the application *)
let app_value (adm: app_data_model) = AppDataModel?.value adm

(* TODO: uncomment out TKey after the previous todo is completed (key is generalized) *)
let rec interp_code (adm: app_data_model) (c:code) : eqtype =
  match c with
  | TUnit -> unit
  | TUInt8 -> u8
  | TUInt16 -> u16
  | TUInt32 -> u32
  | TUInt64 -> u64
  (* | TKey -> app_key adm *)
  | TValue -> app_value adm
  | TPair c1 c2 -> interp_code adm c1 & interp_code adm c2

(*
 * The function table
 *
 * Type of function identifiers
 *)
type fn_id = u8

(* data value with the option of a null type *)
type app_value_nullable (adm: app_data_model) =
  | Null: app_value_nullable adm
  | DValue: v: app_value adm -> app_value_nullable adm

(* an application record is a key-value pair *)
type app_record (adm: app_data_model) = app_key adm & app_value_nullable adm

(* the application state *)
let app_state (adm: app_data_model) = (k: app_key adm) -> app_value_nullable adm

(*
 * fn_sig is the signature that each function id in the table is mapped to
 *
 * It is parametrized by a, the type of the application specific state
 *
 * It contains the argument and result type of the function (their codes)
 *
 * f is the actual function
 *   it takes as input an argument of type (interp_code farg_t),
 *   a store st
 *     it must be the case that the footprint of f is contained in the store,
 *   and an application specific state
 *
 *   f then returns a result value (of type (interp_code fres_t)), and a new store and app state
 *)
type fn_return_code =
  | Fn_success
  | Fn_failure

noeq
type fn_sig (adm: app_data_model) (a:Type) = {
  (* code of the argument of the function *)
  farg_t : code;

  (* code encoding the result type of the function *)
  fres_t : code;

  (*
   * the actual function that takes in the argument, a list of records
   * and returns a list of records, a succ/failure, a result, and
   * new internal state a
   *)
  f : arg:interp_code adm farg_t ->
      list (app_record adm) ->
      a ->
      (fn_return_code & interp_code adm fres_t & a & list (app_record adm));
}

(*
 * Finally the function table is a map from functions ids to signatures
 *)
type fn_tbl (adm: app_data_model) (a:Type) = Map.t fn_id (fn_sig adm a)

(*
 * The application parameters: an application specific state type and a function table
 *)
noeq
type app_params = {
  app_int_state: Type;
  ainit: app_int_state;
  adm: app_data_model;
  tbl : fn_tbl adm app_int_state;
  // keyhashfn: app_key adm -> data_key;
  valuehashfn: app_value adm -> hash_value
}

(* the type of valid function ids of an application *)
let appfn_id (aprm: app_params) = (fid: fn_id {Map.contains aprm.tbl fid})

(* argument type of a function *)
let appfn_arg (#aprm: app_params) (fid: appfn_id aprm): eqtype =
  let fnsig = Map.sel aprm.tbl fid in
  interp_code aprm.adm fnsig.farg_t

(* return type of a function *)
let appfn_res (#aprm: app_params) (fid: appfn_id aprm): eqtype =
  let fnsig = Map.sel aprm.tbl fid in
  interp_code aprm.adm fnsig.fres_t
