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
= x.base_key_significant_digits `U16.lt` 256us

inline_for_extraction
noextract
let internal_key_synth
  (x: LP.parse_filter_refine internal_key_filter)
: Tot internal_key
= Zeta.Steel.LogEntry.Types.Mkbase_key
    (Zeta.Steel.LogEntry.Types.Mku256 x.base_key_k.v3 x.base_key_k.v2 x.base_key_k.v1 x.base_key_k.v0)
    x.base_key_significant_digits

inline_for_extraction
noextract
let internal_key_synth_recip
  (x: internal_key)
: Tot (LP.parse_filter_refine internal_key_filter)
= let Zeta.Steel.LogEntry.Types.Mkbase_key (Zeta.Steel.LogEntry.Types.Mku256 v3 v2 v1 v0) sd = x in
  { base_key_k = { v3 = v3; v2 = v2; v1 = v1; v0 = v0; }; base_key_significant_digits = sd }

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

let internal_key_parser32 =
  LS.parse32_synth'
    _
    _
    (LS.parse32_filter base_key_parser32 _ (fun x -> x.base_key_significant_digits `U16.lt` 256us))
    ()

let internal_key_serializer32 =
  LS.serialize32_synth'
    _
    _
    _
    (LS.serialize32_filter base_key_serializer32 _)
    _
    ()

let internal_key_size32 =
  LS.size32_synth'
    _
    _
    _
    (LS.size32_filter base_key_size32 _)
    _
    ()

let internal_key_validator =
  admit () // TODO: need to read the significant_digits field
