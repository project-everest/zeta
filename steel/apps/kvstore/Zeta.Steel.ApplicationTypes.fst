module Zeta.Steel.ApplicationTypes

module KVS = Zeta.KeyValueStore.Spec
module KVF = Zeta.KeyValueStore.Formats

/// Implementation of the Zeta.Steel.ApplicationsTypes interface

type key_type = KVS.key_t

let spec_parser_key = KVF.key_spec_parser
let parse_key = KVF.key_parser
let spec_serializer_key = KVF.key_spec_serializer
let serialize_key = KVF.key_serializer

let spec_parser_key_injective b1 b2 = admit ()

let spec_parser_key_strong_prefix b1 b2 = admit ()

let serialized_key_length v = admit ()

type value_type = KVS.value_t

let eq_value_type v0 v1 = admit ()

let spec_parser_value = KVF.value_spec_parser
let parse_value = KVF.value_parser

let spec_serializer_value = KVF.value_spec_serializer
let serialize_value = KVF.value_serializer

let spec_parser_value_injective b1 b2 = admit ()

let spec_parser_value_strong_prefix b1 b2 = admit ()

let serialized_value_length v = admit ()

let aprm = KVS.kv_params

// TODO
let store_size = FStar.UInt16.uint_to_t (FStar.UInt.max_int 16)
let n_threads = FStar.UInt32.uint_to_t (FStar.UInt.max_int 15)


/// For application function args, e.g. vget, Zeta.KeyValueStore.Formats gives us
///   a parser and serializer for the record type
///
/// But ApplicationTypes requires a generic parser of type app_args fid & slots fid
///
/// We can write a total function on the parser output,
///   but I guess to prove injectivity etc. of the resulting parser,
///   we would need synth_injective like properties
///
/// We prove those below, but they are not connected to the code right now

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

let vget_args_synth_f (x:KVF.vget_args_t)
  : app_args KVS.vget_id & slots KVS.vget_id
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

let vput_args_synth_f (x:KVF.vput_args_t)
  : app_args KVS.vput_id & slots KVS.vput_id
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
  : P.spec_parser (app_args KVS.vget_id &
                   slots KVS.vget_id)
  = fun b ->
    match KVF.vget_args_spec_parser b with
    | None -> None
    | Some (x, consumed) -> Some (vget_args_synth_f x, consumed)

let vput_args_spec_parser
  : P.spec_parser (app_args KVS.vput_id &
                   slots KVS.vput_id)
  = fun b ->
    match KVF.vput_args_spec_parser b with
    | None -> None
    | Some (x, consumed) -> Some (vput_args_synth_f x, consumed)

let spec_app_parser fid =
  if fid = KVS.vget_id
  then vget_args_spec_parser
  else vput_args_spec_parser

let spec_result_parser fid =
  if fid = KVS.vget_id
  then KVF.vget_result_spec_parser
  else KVF.vput_result_spec_parser

let spec_result_serializer fid =
  if fid = KVS.vget_id
  then KVF.vget_result_spec_serializer
  else KVF.vput_result_spec_serializer

//
// TODO: need to implement using some parser
//       combinators for Zeta.Steel.Parser.spec_parser
//
let spec_app_result_entry_parser = admit ()
let spec_app_result_entry_serializer = admit ()
