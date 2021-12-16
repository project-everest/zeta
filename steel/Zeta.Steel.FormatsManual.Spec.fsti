module Zeta.Steel.FormatsManual.Spec
include Zeta.Steel.ApplicationRecord
include Zeta.Steel.LogEntry.Types
open Zeta.Steel.ApplicationTypes

module P = Zeta.Steel.Parser
val spec_parser_stamped_record : P.spec_parser stamped_record
val spec_serializer_stamped_record : P.spec_serializer spec_parser_stamped_record

/// This is an ad hoc bound due to a bound on Blake hashable inputs
val serialized_stamped_record_length (s:stamped_record)
  : Lemma (Seq.length (spec_serializer_stamped_record s) <= 4096)
