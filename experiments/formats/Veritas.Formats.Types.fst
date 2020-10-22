module Veritas.Formats.Types

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U64 = FStar.UInt64

type slot_id = U16.t

type u256 = {
  v3 : U64.t;
  v2 : U64.t;
  v1 : U64.t;
  v0 : U64.t;
}

type key = {
  k : u256;
  significant_digits : U8.t;
}

type data_t = u256

type voption =
  | Vnone
  | Vsome

type data_value =
  | Dv_vnone of unit
  | Dv_vsome of data_t

type hash_value = u256

type vbool =
  | Vfalse
  | Vtrue

type descendent_hash_desc = {
  dhd_key : key;
  dhd_h : hash_value;
  evicted_to_blum : vbool;
}

type descendent_hash =
  | Dh_vnone of unit
  | Dh_vsome of descendent_hash_desc

type value_kind =
  | Mval
  | Dval

type mval_value = {
  l : descendent_hash;
  r : descendent_hash;
}

type value =
  | V_mval of mval_value
  | V_dval of data_value

type add_method =
  | MAdd
  | BAdd

type record = {
  record_key : key;
  record_value : value;
  record_add_method : add_method;
  record_l_child_in_store : vbool;
  record_r_child_in_store : vbool;
}

type vlog_entry_kind =
  | Get
  | Put
  | AddM
  | EvictM
  | AddB
  | EvictB
  | EvictBM

type vlog_entry_get_put = {
  vegp_s : slot_id;
  vegp_v : data_value;
}

type vlog_entry_addm = {
  veam_s : slot_id;
  veam_r : record;
  veam_s2 : slot_id;
}

type vlog_entry_evictm = {
  veem_s : slot_id;
  veem_s2 : slot_id;
}

type timestamp = U64.t

type thread_id = U16.t

type vlog_entry_addb = {
  veab_s : slot_id;
  veab_r : record;
  veab_t : timestamp;
  veab_j : thread_id;
}

type vlog_entry_evictb = {
  veeb_s : slot_id;
  veeb_t : timestamp;
}

type vlog_entry_evictbm = {
  veebm_s : slot_id;
  veebm_s2 : slot_id;
  veebm_t : timestamp;
}

type vlog_entry =
  | Ve_Get of vlog_entry_get_put
  | Ve_Put of vlog_entry_get_put
  | Ve_AddM of vlog_entry_addm
  | Ve_EvictM of vlog_entry_evictm
  | Ve_AddB of vlog_entry_addb
  | Ve_EvictB of vlog_entry_evictb
  | Ve_EvictBM of vlog_entry_evictbm
