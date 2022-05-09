module Zeta.Formats.Aux.Base_key

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

let synth_raw_key
  (x: Zeta.Formats.Aux.Raw_key.raw_key)
: Tot Zeta.Steel.KeyUtils.raw_key
= {
  Zeta.Steel.KeyUtils.k = Zeta.Formats.Synth.U256.synth_u256 x.raw_key_k;
  significant_digits = x.raw_key_significant_digits;
}

inline_for_extraction
noextract
let base_key_filter
  (x: Zeta.Formats.Aux.Raw_key.raw_key)
: Tot bool
= Zeta.Steel.KeyUtils.good_raw_key_impl (synth_raw_key x)

inline_for_extraction
noextract
let base_key_synth
  (x: LP.parse_filter_refine base_key_filter)
: Tot base_key
= synth_raw_key x

let synth_raw_key_recip
  (x: Zeta.Steel.KeyUtils.raw_key)
: Tot Zeta.Formats.Aux.Raw_key.raw_key
= {
  Zeta.Formats.Aux.Raw_key.raw_key_k = Zeta.Formats.Synth.U256.synth_u256_recip x.k;
  raw_key_significant_digits = x.significant_digits;
}

inline_for_extraction
noextract
let base_key_synth_recip
  (x: base_key)
: Tot (LP.parse_filter_refine base_key_filter)
= synth_raw_key_recip x

let base_key_parser =
  LP.parse_synth
    (LP.parse_filter Zeta.Formats.Aux.Raw_key.raw_key_parser base_key_filter)
    base_key_synth

let base_key_serializer =
  LP.serialize_synth
    _
    _
    (LP.serialize_filter Zeta.Formats.Aux.Raw_key.raw_key_serializer base_key_filter)
    base_key_synth_recip
    ()

let base_key_bytesize _ = 34

let base_key_bytesize_eq _ = ()

let base_key_parser32 =
  LS.parse32_synth'
    _
    _
    (LS.parse32_filter Zeta.Formats.Aux.Raw_key.raw_key_parser32 _ (fun x -> base_key_filter x))
    ()

let base_key_serializer32 =
  LS.serialize32_synth'
    _
    _
    _
    (LS.serialize32_filter Zeta.Formats.Aux.Raw_key.raw_key_serializer32 _)
    _
    ()

let base_key_size32 =
  LS.size32_constant
    base_key_serializer
    34ul
    ()

let base_key_validator =
  LL.validate_synth
    (LL.validate_filter Zeta.Formats.Aux.Raw_key.raw_key_validator Zeta.Formats.Aux.Raw_key.raw_key_reader _ (fun x -> base_key_filter x))
    _
    ()

let base_key_reader =
  LL.read_synth'
    _
    base_key_synth
    (LL.read_filter Zeta.Formats.Aux.Raw_key.raw_key_reader base_key_filter)
    ()

let base_key_lserializer =
  LL.serialize32_synth
    (LL.serialize32_filter Zeta.Formats.Aux.Raw_key.raw_key_lserializer base_key_filter)
    base_key_synth
    base_key_synth_recip
    (fun x -> base_key_synth_recip x)
    ()
