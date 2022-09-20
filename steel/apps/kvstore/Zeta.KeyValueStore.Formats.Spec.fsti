module Zeta.KeyValueStore.Formats.Spec
include Zeta.KeyValueStore.Formats.Types

module A = Zeta.App
module P = Zeta.Steel.Parser

val key_spec_parser : P.spec_parser key_t

val key_spec_serializer : P.spec_serializer key_spec_parser

val key_spec_parser_injective (b1 b2: _) : Lemma
  (requires (match key_spec_parser b1, key_spec_parser b2 with
  | Some (v1, n1), Some (v2, n2) -> v1 == v2
  | _ -> False
  ))
  (ensures (match key_spec_parser b1, key_spec_parser b2 with
  | Some (v1, n1), Some (v2, n2) -> (n1 <: nat) == n2 /\ Seq.slice b1 0 n1 == Seq.slice b2 0 n2
  | _ -> True
  ))

val key_spec_parser_strong_prefix (b1 b2: _) : Lemma
  (requires (
    match key_spec_parser b1 with
    | Some (_, n1) -> n1 <= Seq.length b2 /\ Seq.slice b1 0 n1 == Seq.slice b2 0 n1
    | _ -> False
  ))
  (ensures (
    match key_spec_parser b1, key_spec_parser b2 with
    | Some (v1, _), Some (v2, _) -> v1 == v2
    | _ -> False
  ))

/// This is an ad hoc bound due to a bound on Blake hashable inputs
/// FIXME: this bound is necessary because QuackyDucky expects a constant bound on abstract types
val serialized_key_length (v:key_t)
  : Lemma (Seq.length (key_spec_serializer v) <= 2040)

val value_spec_parser : P.spec_parser value_t

val value_spec_serializer : P.spec_serializer value_spec_parser

val value_spec_parser_injective (b1 b2: _) : Lemma
  (requires (match value_spec_parser b1, value_spec_parser b2 with
  | Some (v1, n1), Some (v2, n2) -> v1 == v2
  | _ -> False
  ))
  (ensures (match value_spec_parser b1, value_spec_parser b2 with
  | Some (v1, n1), Some (v2, n2) -> (n1 <: nat) == n2 /\ Seq.slice b1 0 n1 == Seq.slice b2 0 n2
  | _ -> True
  ))

val value_spec_parser_strong_prefix (b1 b2: _) : Lemma
  (requires (
    match value_spec_parser b1 with
    | Some (_, n1) -> n1 <= Seq.length b2 /\ Seq.slice b1 0 n1 == Seq.slice b2 0 n1
    | _ -> False
  ))
  (ensures (
    match value_spec_parser b1, value_spec_parser b2 with
    | Some (v1, _), Some (v2, _) -> v1 == v2
    | _ -> False
  ))

/// This is an ad hoc bound due to a bound on Blake hashable inputs
/// FIXME: this bound is necessary because QuackyDucky expects a constant bound on abstract types
val serialized_value_length (v:value_t)
  : Lemma (Seq.length (value_spec_serializer v) <= 2040)

val vget_args_spec_parser : P.spec_parser vget_args_t

val vget_result_spec_parser : P.spec_parser vget_result_t

val vget_result_spec_serializer : P.spec_serializer vget_result_spec_parser

val vput_args_spec_parser : P.spec_parser vput_args_t

val vput_result_spec_parser : P.spec_parser vput_result_t

val vput_result_spec_serializer : P.spec_serializer vput_result_spec_parser

val nullable_value_parser : P.spec_parser value_nullable
