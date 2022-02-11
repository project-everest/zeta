module Zeta.Formats.Synth

module LPC = LowParse.Spec.Combinators

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

val synth_value
  (x: Zeta.Formats.Aux.Value.value)
: Tot Zeta.Steel.LogEntry.Types.value

val synth_value_recip
  (x: Zeta.Steel.LogEntry.Types.value)
: Tot Zeta.Formats.Aux.Value.value

val synth_value_injective
: squash (LPC.synth_injective synth_value)

val synth_value_inverse
: squash (LPC.synth_inverse synth_value synth_value_recip)
