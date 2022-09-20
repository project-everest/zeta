module Zeta.Formats.Aux.Internal_key

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module LP = LowParse.Spec
module LS = LowParse.SLow
module LPI = LowParse.Spec.AllIntegers
module LL = LowParse.Low
module L = FStar.List.Tot
module B = LowStar.Buffer
module BY = FStar.Bytes
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

friend Zeta.Formats.Aux.External
open Zeta.Formats.Aux.External
open Zeta.Formats.Aux.Base_key

inline_for_extraction
noextract
let internal_key_filter
  (x: base_key)
: Tot bool
= Zeta.Steel.KeyUtils.is_internal_key x

inline_for_extraction
noextract
let internal_key_synth
  (x: LP.parse_filter_refine internal_key_filter)
: Tot internal_key
= x

inline_for_extraction
noextract
let internal_key_synth_recip
  (x: internal_key)
: Tot (LP.parse_filter_refine internal_key_filter)
= x

open Zeta.Formats.Aux.Base_key

let internal_key_parser =
  LP.parse_synth
    (LP.parse_filter base_key_parser internal_key_filter)
    internal_key_synth

let internal_key_serializer =
  LP.serialize_synth
    _
    _
    (LP.serialize_filter base_key_serializer internal_key_filter)
    internal_key_synth_recip
    ()

let internal_key_bytesize x = base_key_bytesize (internal_key_synth_recip x)

let internal_key_bytesize_eq x =
  LP.serialize_synth_eq _ internal_key_synth (LP.serialize_filter base_key_serializer internal_key_filter)
    internal_key_synth_recip
    () x;
  base_key_bytesize_eq (internal_key_synth_recip x)

let internal_key_size32 =
  LS.size32_synth'
    _
    _
    _
    (LS.size32_filter base_key_size32 _)
    _
    ()

let internal_key_validator =
  LL.validate_synth
    #_ #_ #_
    #(LP.parse_filter base_key_parser internal_key_filter)
    (fun sl pos ->
      let h = HST.get () in
      LL.valid_filter h base_key_parser internal_key_filter sl (LL.uint64_to_uint32 pos);
      let res = base_key_validator sl pos in
      if LL.is_error res
      then res
      else
        let bk = Zeta.Formats.Aux.Base_key.base_key_reader sl (LL.uint64_to_uint32 pos) in
        if Zeta.Steel.KeyUtils.is_internal_key bk
        then res
        else LL.validator_error_generic
    )
    internal_key_synth
    ()

let internal_key_reader =
  LL.read_synth'
    #_ #_ #_
    (LP.parse_filter base_key_parser internal_key_filter)
    internal_key_synth
    (LL.read_filter base_key_reader internal_key_filter)
    ()

let internal_key_lserializer =
  LL.serialize32_synth
    (LL.serialize32_filter base_key_lserializer internal_key_filter)
    internal_key_synth
    internal_key_synth_recip
    (fun x -> internal_key_synth_recip x)
    ()
