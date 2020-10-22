module Veritas.Formats
open Veritas.Formats.EverParse.Slot_id
open Veritas.Formats.EverParse.U256
open Veritas.Formats.EverParse.Key
open Veritas.Formats.EverParse.Data_value
open Veritas.Formats.EverParse.Hash_value
open Veritas.Formats.EverParse.Vbool
open Veritas.Formats.EverParse.Descendent_hash_desc
open Veritas.Formats.EverParse.Descendent_hash
open Veritas.Formats.EverParse.Mval_value
open Veritas.Formats.EverParse.Value
open Veritas.Formats.EverParse.Add_method
open Veritas.Formats.EverParse.Record
open Veritas.Formats.EverParse.Vlog_entry_get_put
open Veritas.Formats.EverParse.Vlog_entry_addm
open Veritas.Formats.EverParse.Vlog_entry_evictm
open Veritas.Formats.EverParse.Timestamp
open Veritas.Formats.EverParse.Thread_id
open Veritas.Formats.EverParse.Vlog_entry_addb
open Veritas.Formats.EverParse.Vlog_entry_evictb
open Veritas.Formats.EverParse.Vlog_entry_evictbm
open Veritas.Formats.EverParse.Vlog_entry

let extract_log_entry l =
  let sl = LP.make_slice l.buf l.len in
  let pos = B.index l.pos 0ul in
  let pos' = vlog_entry_validator sl (FStar.Int.Cast.uint32_to_uint64 pos) in
  if LowParse.Low.Base.is_error pos'
  then None // raise "extract_log_entry: no valid log entry"
  else begin
    B.upd l.pos 0ul (LP.uint64_to_uint32 pos');
    Some (vlog_entry_reader sl pos)
  end
