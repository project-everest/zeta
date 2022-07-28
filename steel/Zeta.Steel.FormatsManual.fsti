module Zeta.Steel.FormatsManual
include Zeta.Steel.LogEntry.Types
(* This file should eventually be generated by EverParse and renamed
   to Zeta.Steel.Formats *)
open Zeta.Steel.ApplicationTypes
module KU = Zeta.Steel.KeyUtils

/// Factored into another module?

module U16 = FStar.UInt16

let slot = x:slot_id{ U16.v x < U16.v store_size }

let is_internal_key_for_data (k:base_key)
  : bool
  = KU.is_data_key k

let is_internal_key_root (k:base_key)
  : bool
  = KU.is_root k

module P = Zeta.Steel.Parser
val parse_app_record: P.parser Zeta.Steel.ApplicationRecord.spec_parser_app_record

let eq_vbool (v0 v1: vbool)
  : Tot (b:bool { b <==>  (v0 == v1) })
  = match v0, v1 with
    | Vfalse, Vfalse
    | Vtrue, Vtrue -> true
    | _ -> false

let eq_descendent_hash_desc (v0 v1: descendent_hash_desc)
  : (b:bool { b <==> (v0 == v1) })
  = KU.eq_base_key v0.dhd_key v1.dhd_key &&
    KU.eq_u256 v0.dhd_h v1.dhd_h &&
    eq_vbool v0.evicted_to_blum v1.evicted_to_blum
  
let eq_descendent_hash (v0 v1: descendent_hash)
  : (b:bool { b <==> (v0 == v1) })
  = match v0, v1 with
    | Dh_vnone _, Dh_vnone _ -> true
    | Dh_vsome v0, Dh_vsome v1 -> eq_descendent_hash_desc v0 v1
    | _ -> false
  
let eq_mval_value (v0 v1:mval_value)
  : (b:bool { b <==> (v0 == v1) })
  = eq_descendent_hash v0.l v1.l &&
    eq_descendent_hash v0.r v1.r
    
let eq_value (v0 v1:value)
  : (b:bool { b <==> (v0 == v1) })
  = match v0, v1 with
    | MValue mv0, MValue mv1 -> eq_mval_value mv0 mv1
    | DValue None, DValue None -> true
    | DValue (Some vt0), DValue (Some vt1) -> eq_value_type vt0 vt1
    | _ -> false

