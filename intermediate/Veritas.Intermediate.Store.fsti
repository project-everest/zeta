module Veritas.Intermediate.Store
open FStar.Integers
open Veritas.Intermediate.Common
module U16 = FStar.UInt16

let vstore = Seq.lseq (option record) (UInt.max_int U16.n)

let get_record (st:vstore) (s:slot_id)
  : option record
  = Seq.index st (U16.v s)

let has_record (st:vstore) (s:slot_id)
  : bool
  = Some? (get_record st s)

let update_record (st:vstore) (s:slot_id) (r:record)
  : vstore
  = Seq.upd st (U16.v s) (Some r)

let add_record (st:vstore) (s:slot_id) (k:key) (v:value{is_value_of k v}) (a:add_method)
  : vstore
  = update_record st s (mk_record k v a)

let evict_record (st:vstore) (s:slot_id) (k:key)  //AR: Do we need k here?
  : vstore
  = Seq.upd st (U16.v s) None
