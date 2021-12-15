module Zeta.Formats.Aux.Significant_digits_t

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

inline_for_extraction
noextract
let significant_digits_filter
  (x: U16.t)
: Tot bool
= x `U16.lte` 256us

inline_for_extraction
noextract
let significant_digits_synth
  (x: LP.parse_filter_refine significant_digits_filter)
: Tot significant_digits_t
= x

inline_for_extraction
noextract
let significant_digits_synth_recip
  (x: significant_digits_t)
: Tot (LP.parse_filter_refine significant_digits_filter)
= x

let significant_digits_t_parser =
  LP.parse_synth
    (LP.parse_filter LP.parse_u16 significant_digits_filter)
    significant_digits_synth

let significant_digits_t_serializer =
  LP.serialize_synth
    _
    _
    (LP.serialize_filter LP.serialize_u16 significant_digits_filter)
    significant_digits_synth_recip
    ()

let significant_digits_t_bytesize _ = 2

let significant_digits_t_bytesize_eq _ = ()

let significant_digits_t_parser32 =
  LS.parse32_synth'
    _
    _
    (LS.parse32_filter LS.parse32_u16 _ (fun x -> x `U16.lte` 256us))
    ()

let significant_digits_t_serializer32 =
  LS.serialize32_synth'
    _
    _
    _
    (LS.serialize32_filter LS.serialize32_u16 _)
    _
    ()

let significant_digits_t_size32 =
  LS.size32_constant
    significant_digits_t_serializer
    2ul
    ()

let significant_digits_t_validator =
  LL.validate_synth
    (LL.validate_filter (LL.validate_u16 ()) LL.read_u16 _ (fun x -> x `U16.lte` 256us))
    _
    ()

let significant_digits_t_reader =
  LL.read_synth'
    _
    significant_digits_synth
    (LL.read_filter LL.read_u16 significant_digits_filter)
    ()

let significant_digits_t_lserializer =
  LL.serialize32_synth
    (LL.serialize32_filter LL.serialize32_u16 significant_digits_filter)
    significant_digits_synth
    significant_digits_synth_recip
    (fun x -> x)
    ()
