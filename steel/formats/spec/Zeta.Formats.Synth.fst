module Zeta.Formats.Synth

friend Zeta.Formats.Aux.External.App
friend Zeta.Formats.Aux.External

let synth_key
  (x: Zeta.Formats.Aux.Key.key)
: Tot Zeta.Steel.LogEntry.Types.key
= match x with
  | Zeta.Formats.Aux.Key.Key_v_key_internal k -> Zeta.Steel.LogEntry.Types.InternalKey k
  | Zeta.Formats.Aux.Key.Key_v_key_application k -> Zeta.Steel.LogEntry.Types.ApplicationKey k

let synth_key_recip
  (x: Zeta.Steel.LogEntry.Types.key)
: Tot Zeta.Formats.Aux.Key.key
= match x with
  | Zeta.Steel.LogEntry.Types.InternalKey k -> Zeta.Formats.Aux.Key.Key_v_key_internal k
  | Zeta.Steel.LogEntry.Types.ApplicationKey k -> Zeta.Formats.Aux.Key.Key_v_key_application k

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

let synth_base_key
  (x: Zeta.Formats.Aux.Base_key.base_key)
: Tot Zeta.Steel.LogEntry.Types.base_key
= Zeta.Steel.LogEntry.Types.Mkbase_key
    (synth_u256 x.Zeta.Formats.Aux.Base_key.base_key_k)
    x.Zeta.Formats.Aux.Base_key.base_key_significant_digits

let synth_base_key_recip
  (x: Zeta.Steel.LogEntry.Types.base_key)
: Tot Zeta.Formats.Aux.Base_key.base_key
= match x with
  | Zeta.Steel.LogEntry.Types.Mkbase_key k sd ->
    {
      Zeta.Formats.Aux.Base_key.base_key_k = synth_u256_recip k;
      Zeta.Formats.Aux.Base_key.base_key_significant_digits = sd;
    }

let synth_hash_value
  (x: Zeta.Formats.Aux.Hash_value.hash_value)
: Tot Zeta.Steel.LogEntry.Types.hash_value
= synth_u256 x

let synth_hash_value_recip
  (x: Zeta.Steel.LogEntry.Types.hash_value)
: Tot Zeta.Formats.Aux.Hash_value.hash_value
= synth_u256_recip x

let synth_vbool
  (x: Zeta.Formats.Aux.Vbool.vbool)
: Tot Zeta.Steel.LogEntry.Types.vbool
= match x with
  | Zeta.Formats.Aux.Vbool.Vfalse -> Zeta.Steel.LogEntry.Types.Vfalse
  | Zeta.Formats.Aux.Vbool.Vtrue -> Zeta.Steel.LogEntry.Types.Vtrue

let synth_vbool_recip
  (x: Zeta.Steel.LogEntry.Types.vbool)
: Tot Zeta.Formats.Aux.Vbool.vbool
= match x with
  | Zeta.Steel.LogEntry.Types.Vfalse -> Zeta.Formats.Aux.Vbool.Vfalse
  | Zeta.Steel.LogEntry.Types.Vtrue -> Zeta.Formats.Aux.Vbool.Vtrue

let synth_descendent_hash_desc
  (x: Zeta.Formats.Aux.Descendent_hash_desc.descendent_hash_desc)
: Tot Zeta.Steel.LogEntry.Types.descendent_hash_desc
= {
    Zeta.Steel.LogEntry.Types.dhd_key = synth_base_key x.Zeta.Formats.Aux.Descendent_hash_desc.dhd_key;
    Zeta.Steel.LogEntry.Types.dhd_h = synth_hash_value x.Zeta.Formats.Aux.Descendent_hash_desc.dhd_h;
    Zeta.Steel.LogEntry.Types.evicted_to_blum = synth_vbool x.Zeta.Formats.Aux.Descendent_hash_desc.evicted_to_blum;
  }

let synth_descendent_hash_desc_recip
  (x: Zeta.Steel.LogEntry.Types.descendent_hash_desc)
: Tot Zeta.Formats.Aux.Descendent_hash_desc.descendent_hash_desc
= {
    Zeta.Formats.Aux.Descendent_hash_desc.dhd_key = synth_base_key_recip x.Zeta.Steel.LogEntry.Types.dhd_key;
    Zeta.Formats.Aux.Descendent_hash_desc.dhd_h = synth_hash_value_recip
    x.Zeta.Steel.LogEntry.Types.dhd_h;
    Zeta.Formats.Aux.Descendent_hash_desc.evicted_to_blum = synth_vbool_recip x.Zeta.Steel.LogEntry.Types.evicted_to_blum;
  }

let synth_descendent_hash
  (x: Zeta.Formats.Aux.Descendent_hash.descendent_hash)
: Tot Zeta.Steel.LogEntry.Types.descendent_hash
= match x with
  | Zeta.Formats.Aux.Descendent_hash.Dh_vnone _ -> Zeta.Steel.LogEntry.Types.Dh_vnone ()
  | Zeta.Formats.Aux.Descendent_hash.Dh_vsome d ->
    Zeta.Steel.LogEntry.Types.Dh_vsome (synth_descendent_hash_desc d)

let synth_descendent_hash_recip
  (x: Zeta.Steel.LogEntry.Types.descendent_hash)
: Tot Zeta.Formats.Aux.Descendent_hash.descendent_hash
= match x with
  | Zeta.Steel.LogEntry.Types.Dh_vnone () ->
    Zeta.Formats.Aux.Descendent_hash.Dh_vnone ()
  | Zeta.Steel.LogEntry.Types.Dh_vsome d ->
    Zeta.Formats.Aux.Descendent_hash.Dh_vsome (synth_descendent_hash_desc_recip d)

let synth_mval_value
  (x: Zeta.Formats.Aux.Mval_value.mval_value)
: Tot Zeta.Steel.LogEntry.Types.mval_value
= Zeta.Steel.LogEntry.Types.Mkmval_value
    (synth_descendent_hash x.Zeta.Formats.Aux.Mval_value.l)
    (synth_descendent_hash x.Zeta.Formats.Aux.Mval_value.r)

let synth_mval_value_recip
  (x: Zeta.Steel.LogEntry.Types.mval_value)
: Tot Zeta.Formats.Aux.Mval_value.mval_value
= match x with
  | Zeta.Steel.LogEntry.Types.Mkmval_value l r ->
    Zeta.Formats.Aux.Mval_value.Mkmval_value
      (synth_descendent_hash_recip l)
      (synth_descendent_hash_recip r)

let synth_value
  (x: Zeta.Formats.Aux.Value.value)
: Tot Zeta.Steel.LogEntry.Types.value
= match x with
  | Zeta.Formats.Aux.Value.V_payload_DValueNone _ ->
    Zeta.Steel.LogEntry.Types.DValue None
  | Zeta.Formats.Aux.Value.V_payload_DValueSome v ->
    Zeta.Steel.LogEntry.Types.DValue (Some v)
  | Zeta.Formats.Aux.Value.V_payload_MValue v ->
    Zeta.Steel.LogEntry.Types.MValue (synth_mval_value v)

let synth_value_recip
  (x: Zeta.Steel.LogEntry.Types.value)
: Tot Zeta.Formats.Aux.Value.value
= match x with
  | Zeta.Steel.LogEntry.Types.DValue None ->
    Zeta.Formats.Aux.Value.V_payload_DValueNone ()
  | Zeta.Steel.LogEntry.Types.DValue (Some v) ->
    Zeta.Formats.Aux.Value.V_payload_DValueSome v
  | Zeta.Steel.LogEntry.Types.MValue v ->
    Zeta.Formats.Aux.Value.V_payload_MValue (synth_mval_value_recip v)

let synth_record
  (x: Zeta.Formats.Aux.Record.record)
: Tot Zeta.Steel.LogEntry.Types.record
= (synth_key x.Zeta.Formats.Aux.Record.record_key,
    synth_value x.Zeta.Formats.Aux.Record.record_value)

let synth_record_recip
  (x: Zeta.Steel.LogEntry.Types.record)
: Tot Zeta.Formats.Aux.Record.record
= match x with
  | (k, v) ->
    Zeta.Formats.Aux.Record.Mkrecord
      (synth_key_recip k)
      (synth_value_recip v)

let synth_record_injective = ()

#push-options "--ifuel 8"
let synth_record_inverse = ()
#pop-options

