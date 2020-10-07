module Veritas.Intermediate.Store
open FStar.Integers
open Veritas.Intermediate.Common
module U16 = FStar.UInt16
module SA = Veritas.SeqAux

let vstore = Seq.seq (option record)

let get_record (st:vstore) (s:slot_id)
  : option record
  = if s >= Seq.length st then None else Seq.index st s

let store_contains (st:vstore) (s:slot_id)
  : bool
  = Some? (get_record st s)

let update_record (st:vstore) (s:SA.seq_index st) (r:record)
  : vstore
  = Seq.upd st s (Some r)

let add_record (st:vstore) (s:SA.seq_index st) (k:key) (v:value{Veritas.Record.is_value_of k v}) (a:add_method)
  : vstore
  = update_record st s (mk_record k v a)

let evict_record (st:vstore) (s:SA.seq_index st)
  : vstore
  = Seq.upd st s None
