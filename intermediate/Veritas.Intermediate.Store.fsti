module Veritas.Intermediate.Store
open FStar.Integers
open Veritas.Intermediate.Common
module U16 = FStar.UInt16
module SA = Veritas.SeqAux
module R = Veritas.Record

let vstore = Seq.seq (option record)
let st_index (st:vstore) = SA.seq_index st

let get_record (st:vstore) (s:slot_id)
  : option record
  = if s >= Seq.length st then None else Seq.index st s

let contains_record (st:vstore) (s:slot_id)
  : bool
  = Some? (get_record st s)

let update_record (st:vstore) (s:st_index st) (r:record)
  : vstore
  = Seq.upd st s (Some r)

let update_record_value (st:vstore) (s:st_index st{contains_record st s}) (v:value)
  : vstore
  = let Some r = get_record st s in
    update_record st s ({r with record_value = v}) 

let add_record (st:vstore) (s:SA.seq_index st) (k:key) (v:value{Veritas.Record.is_value_of k v}) (a:add_method)
  : vstore
  = update_record st s (mk_record k v a)

let evict_record (st:vstore) (s:SA.seq_index st)
  : vstore
  = Seq.upd st s None
