module Veritas.Intermediate.Logs

module K = Veritas.Key
module MHD = Veritas.MultiSetHashDomain
module R = Veritas.Record
module SA = Veritas.SeqAux
module V = Veritas.Verifier

let slot_id = Veritas.Intermediate.Store.slot_id
let key = K.key
let data_key = K.data_key
let merkle_key = K.merkle_key
let value = R.value
let data_value = R.data_value
let record = R.record
let timestamp = MHD.timestamp
let thread_id = V.thread_id

(* Definitions of different styles of verifier logs.
   - logK : contains only key references (defined in Veritas.Verifier)
   - logSK: contains both slot and key references
   - logS: contains only slot references *)

let logK_entry = V.vlog_entry
let logK = V.vlog

noeq
type logSK_entry =
  | Get_SK: s:slot_id -> k:data_key -> v:data_value -> logSK_entry
  | Put_SK: s:slot_id -> k:data_key -> v:data_value -> logSK_entry
  | AddM_SK: s:slot_id -> r:record -> s':slot_id -> k':merkle_key -> logSK_entry
  | EvictM_SK: s:slot_id -> k:key -> s':slot_id -> k':merkle_key -> logSK_entry
  | AddB_SK: s:slot_id -> r:record -> t:timestamp -> j:thread_id -> logSK_entry
  | EvictB_SK: s:slot_id -> k:key -> t:timestamp -> logSK_entry
  | EvictBM_SK: s:slot_id -> k:key -> s':slot_id -> k':merkle_key -> t:timestamp -> logSK_entry
             
let logSK = Seq.seq logSK_entry

noeq
type logS_entry =
  | Get_S: s:slot_id -> v:data_value -> logS_entry
  | Put_S: s:slot_id -> v:data_value -> logS_entry
  | AddM_S: s:slot_id -> r:record -> s':slot_id -> logS_entry
  | EvictM_S: s:slot_id -> s':slot_id -> logS_entry
  | AddB_S: s:slot_id -> r:record -> t:timestamp -> j:thread_id -> logS_entry
  | EvictB_S: s:slot_id -> t:timestamp -> logS_entry
  | EvictBM_S: s:slot_id -> s':slot_id -> t:timestamp -> logS_entry

let logS = Seq.seq logS_entry

let drop_slots_aux (e:logSK_entry) :logK_entry =
  match e with
  | Get_SK _ k v -> V.Get k v
  | Put_SK _ k v -> V.Put k v
  | AddM_SK _ r _ k' -> V.AddM r k'
  | EvictM_SK _ k _ k' -> V.EvictM k k'
  | AddB_SK _ r t j -> V.AddB r t j
  | EvictB_SK _ k t -> V.EvictB k t
  | EvictBM_SK _ k _ k' t -> V.EvictBM k k' t
  
let drop_slots (l:logSK) : logK 
  = SA.map drop_slots_aux l

// likely similar to EAC: check that for every "OP s k ...", k is the last key added at slot s, and has not been evicted 
let skc (l:logSK) : Type = admit()

// add keys in a way that satisfies skc
let add_consistent_keys (l:logS) : logSK = admit()
