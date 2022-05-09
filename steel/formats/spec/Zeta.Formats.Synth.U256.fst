module Zeta.Formats.Synth.U256

let synth_u256
  (x: Zeta.Formats.Aux.U256.u256)
: Tot Zeta.Steel.LogEntry.Types.u256
= Zeta.Steel.LogEntry.Types.Mku256
    x.Zeta.Formats.Aux.U256.v3
    x.Zeta.Formats.Aux.U256.v2
    x.Zeta.Formats.Aux.U256.v1
    x.Zeta.Formats.Aux.U256.v0

let synth_u256_recip
  (x: Zeta.Steel.LogEntry.Types.u256)
: Tot Zeta.Formats.Aux.U256.u256
= match x with
  | Zeta.Steel.LogEntry.Types.Mku256 v3 v2 v1 v0 ->
    {
      Zeta.Formats.Aux.U256.v3 = v3;
      Zeta.Formats.Aux.U256.v2 = v2;
      Zeta.Formats.Aux.U256.v1 = v1;
      Zeta.Formats.Aux.U256.v0 = v0;
    }
