module Zeta.KeyValueStore.Formats.LowStar

module LL = LowParse.Low
module B = LowStar.Buffer
module HST = FStar.HyperStack.ST

friend Zeta.KeyValueStore.Formats.Spec

let kvstore_key_parser =
  P.make_parser
    key_spec_parser
    LL.parse_u64
    (LL.validate_u64 ())
    LL.read_u64

let kvstore_key_serializer =
  P.make_serializer
    _
    key_spec_serializer
    _
    LL.serialize_u64
    LL.serialize32_u64

let kvstore_value_parser =
  P.make_parser
    value_spec_parser
    LL.parse_u64
    (LL.validate_u64 ())
    LL.read_u64

let kvstore_value_serializer =
  P.make_serializer
    _
    value_spec_serializer
    _
    LL.serialize_u64
    LL.serialize32_u64

let kvstore_vget_args_parser =
  P.make_parser
    vget_args_spec_parser
    parse_vget_args
    (LL.validate_synth
      (LL.validate_u64 () `LL.validate_nondep_then` LL.validate_u64 () `LL.validate_nondep_then` LL.validate_u16 ())
      synth_vget_args
      ()
    )
    (LL.read_synth'
      _
      synth_vget_args
      (LL.read_nondep_then
        (LL.jump_nondep_then LL.jump_u64 LL.jump_u64)
        (LL.read_nondep_then LL.jump_u64 LL.read_u64 LL.read_u64)
        LL.read_u16
      )
      ()
    )

let kvstore_vput_args_parser =
  P.make_parser
    vput_args_spec_parser
    parse_vput_args
    (LL.validate_synth
      (LL.validate_u64 () `LL.validate_nondep_then` LL.validate_u64 () `LL.validate_nondep_then` LL.validate_u16 ())
      synth_vput_args
      ()
    )
    (LL.read_synth'
      _
      synth_vput_args
      (LL.read_nondep_then
        (LL.jump_nondep_then LL.jump_u64 LL.jump_u64)
        (LL.read_nondep_then LL.jump_u64 LL.read_u64 LL.read_u64)
        LL.read_u16
      )
      ()
    )
