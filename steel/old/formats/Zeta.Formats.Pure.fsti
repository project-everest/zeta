module Zeta.Formats.Pure
include Zeta.Formats.Aux
include Zeta.Formats.Types

module U32 = FStar.UInt32
module U8 = FStar.UInt8

val serialize_length : value -> (l: U32.t { U32.v l > 0 })

val parsed: Seq.seq U8.t -> vlog_entry -> prop

val serialize_stamped_record_spec
  (r: stamped_record)
: Ghost (Seq.seq U8.t)
  (requires True)
  (ensures (fun y -> Seq.length y <= 184))

val serialize_stamped_record_injective
  (r1: stamped_record)
  (r2: stamped_record)
: Lemma
  (requires (serialize_stamped_record_spec r1 == serialize_stamped_record_spec r2))
  (ensures (r1 == r2))
