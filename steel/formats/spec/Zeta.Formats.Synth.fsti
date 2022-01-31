module Zeta.Formats.Synth

module LPC = LowParse.Spec.Combinators

val synth_key
  (x: Zeta.Formats.Aux.Key.key)
: Tot Zeta.Steel.LogEntry.Types.key

val synth_key_recip
  (x: Zeta.Steel.LogEntry.Types.key)
: Tot Zeta.Formats.Aux.Key.key

val synth_key_injective
: squash (LPC.synth_injective synth_key)

val synth_key_inverse
: squash (LPC.synth_inverse synth_key synth_key_recip)

val synth_mval_value
  (x: Zeta.Formats.Aux.Mval_value.mval_value)
: Tot Zeta.Steel.LogEntry.Types.mval_value

val synth_mval_value_recip
  (x: Zeta.Steel.LogEntry.Types.mval_value)
: Tot Zeta.Formats.Aux.Mval_value.mval_value

val synth_mval_value_injective
: squash (LPC.synth_injective synth_mval_value)

val synth_mval_value_inverse
: squash (LPC.synth_inverse synth_mval_value synth_mval_value_recip)

val synth_record
  (x: Zeta.Formats.Aux.Record.record)
: Tot Zeta.Steel.LogEntry.Types.record

val synth_record_recip
  (x: Zeta.Steel.LogEntry.Types.record)
: Tot Zeta.Formats.Aux.Record.record

val synth_record_injective
: squash (LPC.synth_injective synth_record)

val synth_record_inverse
: squash (LPC.synth_inverse synth_record synth_record_recip)
