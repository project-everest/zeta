module Zeta.Steel.ApplicationTypes

module S = Zeta.KeyValueStore.Spec
module F = Zeta.KeyValueStore.Formats

/// Implementation of the Zeta.Steel.ApplicationsTypes interface

type key_type = F.key_t

let spec_parser_key = F.key_spec_parser
let parse_key = F.key_parser
let spec_serializer_key = F.key_spec_serializer
let serialize_key = F.key_serializer

let spec_parser_key_injective b1 b2 = admit ()

let spec_parser_key_strong_prefix b1 b2 = admit ()

let serialized_key_length v = admit ()

type value_type = F.value_t

let eq_value_type v0 v1 = admit ()

let spec_parser_value = F.value_spec_parser
let parse_value = F.value_parser

let spec_serializer_value = F.value_spec_serializer
let serialize_value = F.value_serializer

let spec_parser_value_injective b1 b2 = admit ()

let spec_parser_value_strong_prefix b1 b2 = admit ()

let serialized_value_length v = admit ()

let aprm = S.kv_params

let store_size = FStar.UInt16.uint_to_t (FStar.UInt.max_int 16)
let n_threads = FStar.UInt32.uint_to_t (FStar.UInt.max_int 15)

// As in LowParse
let synth_injective
  (#t1: Type)
  (#t2: Type)
  (f: (t1 -> GTot t2))
: GTot Type0
= forall (x x' : t1) . {:pattern (f x); (f x')} f x == f x' ==> x == x'

//
// Move to FStar.Seq
//
let seq_create_injective (#a:Type) (n1 n2:nat) (x y:a)
  : Lemma (Seq.create n1 x == Seq.create n2 y ==> (n1 == n2 /\ x == y))
  = admit ()

/// Synth function for vget args

let vget_args_synth_f (x:F.vget_args_t)
  : app_args S.vget_id & slots S.vget_id
  = (x.vget_key, x.vget_value), Seq.create 1 x.vget_slot

/// Proof of its injectivity

#push-options "--warn_error -271"
let vget_args_synth_f_injective ()
  : Lemma (synth_injective vget_args_synth_f)
  = let aux (#a:Type) (n1 n2:nat) (x y:a)
      : Lemma (Seq.create n1 x == Seq.create n2 y ==> (n1 == n2 /\ x == y))
              [SMTPat ()]
      = seq_create_injective n1 n2 x y in
    ()
#pop-options


/// Synth function for vput args

let vput_args_synth_f (x:F.vput_args_t)
  : app_args S.vput_id & slots S.vput_id
  = (x.vput_key, x.vput_value), Seq.create 1 x.vput_slot


/// Proof of its injectivity

#push-options "--warn_error -271"
let vput_args_synth_f_injective ()
  : Lemma (synth_injective vput_args_synth_f)
  = let aux (#a:Type) (n1 n2:nat) (x y:a)
      : Lemma (Seq.create n1 x == Seq.create n2 y ==> (n1 == n2 /\ x == y))
              [SMTPat ()]
      = seq_create_injective n1 n2 x y in
    ()
#pop-options

let vget_args_spec_parser
  : P.spec_parser (app_args S.vget_id &
                   slots S.vget_id)
  = fun b ->
    match F.vget_args_spec_parser b with
    | None -> None
    | Some (x, consumed) -> Some (vget_args_synth_f x, consumed)

let vput_args_spec_parser
  : P.spec_parser (app_args S.vput_id &
                   slots S.vput_id)
  = fun b ->
    match F.vput_args_spec_parser b with
    | None -> None
    | Some (x, consumed) -> Some (vput_args_synth_f x, consumed)

let spec_app_parser fid =
  if fid = S.vget_id
  then vget_args_spec_parser
  else vput_args_spec_parser

let spec_result_parser fid =
  if fid = S.vget_id
  then F.vget_result_spec_parser
  else F.vput_result_spec_parser

let spec_result_serializer fid =
  if fid = S.vget_id
  then F.vget_result_spec_serializer
  else F.vput_result_spec_serializer

//
// TODO: need to implement using some parser
//       combinators for Zeta.Steel.Parser.spec_parser
//
let spec_app_result_entry_parser = admit ()
let spec_app_result_entry_serializer = admit ()
