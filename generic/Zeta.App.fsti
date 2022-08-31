module Zeta.App

open FStar.Seq
open Zeta.Hash
open Zeta.Key
open Zeta.MultiSet
open Zeta.SeqAux

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
  | TKey
  | TValue
  | TPair : code -> code -> code

(*
 * the application data model specifies the codes for key and data.
 * Currently, the keys are hard-coded to 256 bit vectors.
 *)
noeq type app_data_model =
  | AppDataModel: key: eqtype -> value: eqtype -> app_data_model

(* key type of the application *)
let app_key (adm: app_data_model) = AppDataModel?.key adm

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
  | TKey -> app_key adm
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


(* every key in a sequence of records is distinct *)
let distinct_keys #adm (sk: seq (app_record adm)) =
  forall (i1 i2: seq_index sk). i1 <> i2 ==> (let k1,_ = index sk i1 in
                                         let k2,_ = index sk i2 in
                                         k1 <> k2)

(*
 * Type of the actual function that takes in the argument, an input sequence
 * of records, and returns a succ/failure, a result, a new internal
 * state, and updated values for the input records.
 *)
type app_fn_t (adm:app_data_model) (farg_t:code) (fres_t:code) (arity:nat) =
  arg:interp_code adm farg_t ->
  inp:seq (app_record adm){length inp == arity /\ distinct_keys inp} ->
  fn_return_code &
  interp_code adm fres_t &
  out:seq (app_value_nullable adm){length out == arity}

noeq
type fn_sig (adm: app_data_model) = {
  (* code of the argument of the function *)
  farg_t : code;

  (* code encoding the result type of the function *)
  fres_t : code;

  (* number of records touched by the function *)
  arity: nat;

  (* whether this function writes to the output log *)
  writes_output_log: bool;

  (* the actual function *)
  f : app_fn_t adm farg_t fres_t arity
}

(*
 * Finally the function table is a map from functions ids to signatures
 *)
type fn_tbl (adm: app_data_model) = Map.t fn_id (fn_sig adm)

(*
 * The application parameters: an application specific state type and a function table
 *)
noeq
type app_params = {
  adm: app_data_model;
  tbl : fn_tbl adm;
  keyhashfn: app_key adm -> leaf_key;
  valuehashfn: app_value_nullable adm -> hash_value;
  keycmp: cmp (app_key adm);
  valcmp: cmp (app_value_nullable adm);
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

(* the arity of a function *)
let appfn_arity (#aprm: app_params) (fid: appfn_id aprm): nat =
  let fnsig = Map.sel aprm.tbl fid in
  fnsig.arity

(* the type of read-set of a function call *)
let appfn_rs_t (#aprm: app_params) (fid: appfn_id aprm) =
  let adm = aprm.adm in
  let record_t = app_record adm in
  let arity = appfn_arity fid in
  (inp: seq (record_t) {length inp = arity /\ distinct_keys #adm inp})

(* the type of writes of a function call *)
let appfn_ws_t (#aprm: app_params) (fid: appfn_id aprm) =
  let adm = aprm.adm in
  let value_t = app_value_nullable adm in
  let arity = appfn_arity fid in
  out:seq (value_t){length out = arity}

(* 
 * F* does not type check this without an explicit return type
 *
 * Because fnsig escapes in the return type,
 *   so we need an explicit annotation
 *)
let appfn (#aprm: app_params) (fid: appfn_id aprm):
  (let fn_sig = Map.sel aprm.tbl fid in
   app_fn_t aprm.adm fn_sig.farg_t fn_sig.fres_t fn_sig.arity)
  =
  let fnsig = Map.sel aprm.tbl fid in
  fnsig.f
