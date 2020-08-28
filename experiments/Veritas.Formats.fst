module Veritas.Formats
include Veritas.Formats.Uint16_is_max
include Veritas.Formats.Slot_id
include Veritas.Formats.U256
include Veritas.Formats.Key
include Veritas.Formats.Data_value
include Veritas.Formats.Hash_value
include Veritas.Formats.Vbool
include Veritas.Formats.Descendent_hash_desc
include Veritas.Formats.Descendent_hash
include Veritas.Formats.Mval_value
include Veritas.Formats.Value
include Veritas.Formats.Add_method
include Veritas.Formats.Record
include Veritas.Formats.Vlog_entry_get_put
include Veritas.Formats.Vlog_entry_addm
include Veritas.Formats.Vlog_entry_evictm
include Veritas.Formats.Timestamp
include Veritas.Formats.Thread_id
include Veritas.Formats.Vlog_entry_addb
include Veritas.Formats.Vlog_entry_evictb
include Veritas.Formats.Vlog_entry_evictbm
include Veritas.Formats.Vlog_entry

module U16 = FStar.UInt16

inline_for_extraction
let get_slot_id (s: slot_id) : Tot (x: U16.t { U16.v x < UInt.max_int U16.n }) =
  Sid_prf_Unknown_uint16_is_max?.v s

inline_for_extraction
let make_slot_id (x: U16.t { U16.v x < UInt.max_int U16.n }) : Tot slot_id =
  Sid_prf_Unknown_uint16_is_max x ()

inline_for_extraction
let bool_of_vbool (x: vbool) : Tot bool =
  match x with
  | Vfalse -> false
  | Vtrue -> true

inline_for_extraction
let vbool_of_bool (x: bool) : Tot vbool =
  if x then Vtrue else Vfalse

