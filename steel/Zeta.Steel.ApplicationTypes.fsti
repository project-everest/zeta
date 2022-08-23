module Zeta.Steel.ApplicationTypes
(**
 * This interface will be instantiated by each Zeta application
 * It requires a
 *
 *    - Type of application-specific keys
 *    - Type of application-specific values
 *    - A serializer for keys and values
 *
 * Applications also need to provide a function to run each state
 * transition. See Zeta.Steel.Application for that.

 * This module provides only the types, so that which are in scope
 * everywhere in the Steel implementation of the Zete framework.
 **)
module A = Zeta.App
module P = Zeta.Steel.Parser
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32

let bytes = FStar.Seq.seq U8.t

/// The type of application keys
///   //maybe should not be an eqtype,
///   //instead provide a function to decide equality
///   //nope: QuackyDucky requires eqtype
val key_type : eqtype

/// A parser and serializer of keys
val spec_parser_key : P.spec_parser key_type
val parse_key : P.parser spec_parser_key

val spec_serializer_key : P.spec_serializer spec_parser_key
val serialize_key : P.serializer spec_serializer_key

// BEGIN properties needed to link with EverParse-generated record parsers and serializers

val spec_parser_key_injective (b1 b2: bytes) : Lemma
  (requires (match spec_parser_key b1, spec_parser_key b2 with
  | Some (v1, n1), Some (v2, n2) -> v1 == v2
  | _ -> False
  ))
  (ensures (match spec_parser_key b1, spec_parser_key b2 with
  | Some (v1, n1), Some (v2, n2) -> (n1 <: nat) == n2 /\ Seq.slice b1 0 n1 == Seq.slice b2 0 n2
  | _ -> True
  ))

val spec_parser_key_strong_prefix (b1 b2: bytes) : Lemma
  (requires (
    match spec_parser_key b1 with
    | Some (_, n1) -> n1 <= Seq.length b2 /\ Seq.slice b1 0 n1 == Seq.slice b2 0 n1
    | _ -> False
  ))
  (ensures (
    match spec_parser_key b1, spec_parser_key b2 with
    | Some (v1, _), Some (v2, _) -> v1 == v2
    | _ -> False
  ))

/// This is an ad hoc bound due to a bound on Blake hashable inputs
/// FIXME: this bound is necessary because QuackyDucky expects a constant bound on abstract types
val serialized_key_length (v:key_type)
  : Lemma (Seq.length (spec_serializer_key v) <= 2040)

// END properties needed to link with EverParse-generated record parsers and serializers

/// The type of application values
///   // may not need to be an eqtype
val value_type : eqtype

val eq_value_type (v0 v1:value_type)
  : (b:bool { b <==> (v0 == v1) })

/// A parser and serializer of values
val spec_parser_value : P.spec_parser value_type
val parse_value : P.parser spec_parser_value

val spec_serializer_value : P.spec_serializer spec_parser_value
val serialize_value : P.serializer spec_serializer_value
// BEGIN properties needed to link with EverParse-generated record parsers and serializers

val spec_parser_value_injective (b1 b2: bytes) : Lemma
  (requires (match spec_parser_value b1, spec_parser_value b2 with
  | Some (v1, n1), Some (v2, n2) -> v1 == v2
  | _ -> False
  ))
  (ensures (match spec_parser_value b1, spec_parser_value b2 with
  | Some (v1, n1), Some (v2, n2) -> (n1 <: nat) == n2 /\ Seq.slice b1 0 n1 == Seq.slice b2 0 n2
  | _ -> True
  ))

val spec_parser_value_strong_prefix (b1 b2: bytes) : Lemma
  (requires (
    match spec_parser_value b1 with
    | Some (_, n1) -> n1 <= Seq.length b2 /\ Seq.slice b1 0 n1 == Seq.slice b2 0 n1
    | _ -> False
  ))
  (ensures (
    match spec_parser_value b1, spec_parser_value b2 with
    | Some (v1, _), Some (v2, _) -> v1 == v2
    | _ -> False
  ))

/// This is an ad hoc bound due to a bound on Blake hashable inputs
val serialized_value_length (v:value_type)
  : Lemma (Seq.length (spec_serializer_value v) <= 2040)

// END properties needed to link with EverParse-generated record parsers and serializers

/// The type of high-level app_params, with key and value type
/// instantiated to the above types
let app_params = a:A.app_params{
  a.adm.key == key_type /\
  a.adm.value == value_type
}

/// An instance of an app_params, used for spec
val aprm : app_params

/// The number of entries in the verifier store,
/// configurable per application
val store_size : n:U16.t {U16.v n > 0}

/// The number of verifier threads to use
val n_threads : n:U32.t{ 0 < U32.v n /\ U32.v n < FStar.UInt.max_int 16 }

let tid : eqtype = n:U16.t { U16.v n < U32.v n_threads }

let app_args (fid:A.appfn_id aprm) =
  let fsig = Map.sel aprm.A.tbl fid in
  A.interp_code aprm.A.adm fsig.farg_t

let app_records (fid:A.appfn_id aprm) =
  recs:Seq.seq (A.app_record aprm.A.adm) {
    let fsig = Map.sel aprm.A.tbl fid in
    Seq.length recs == fsig.arity /\
    A.distinct_keys recs
  }

let app_result (fid:A.appfn_id aprm) =
  let fsig = Map.sel aprm.A.tbl fid in
  A.interp_code aprm.A.adm fsig.fres_t

let slots (fid:A.appfn_id aprm) =
  slots:Seq.seq U16.t {
    let fsig = Map.sel aprm.A.tbl fid in
    Seq.length slots == fsig.arity
  }

(* A specifiational parser for the arguments of an app function *)
val spec_app_parser (fid:A.appfn_id aprm)
  : P.spec_parser (app_args fid & slots fid)

val spec_result_parser (fid:A.appfn_id aprm)
  : P.spec_parser (app_result fid)

val spec_result_serializer (fid:A.appfn_id aprm)
  : P.spec_serializer (spec_result_parser fid)

let app_result_entry =
  (fid:A.appfn_id aprm &
   app_args fid &
   app_records fid &
   app_result fid)

(* A specifiational parser for the arguments of an app function *)
val spec_app_result_entry_parser
  : P.spec_parser app_result_entry

val spec_app_result_entry_serializer
  : P.spec_serializer spec_app_result_entry_parser
