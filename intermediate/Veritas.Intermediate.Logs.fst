module Veritas.Intermediate.Logs

open Veritas.Key
open Veritas.MultiSetHashDomain
open Veritas.Record
open Veritas.SeqAux
open Veritas.Intermediate.StoreSKC

module Spec = Veritas.Verifier

let thread_id = Spec.thread_id

(* Definitions of different styles of verifier logs.
   - logK : contains only key references (defined in Veritas.Verifier)
   - logSK: contains both slot and key references
   - logS: contains only slot references *)

let logK_entry = Spec.vlog_entry
let logK = Spec.vlog

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
  | Get_SK _ k v -> Spec.Get k v
  | Put_SK _ k v -> Spec.Put k v
  | AddM_SK _ r _ k' -> Spec.AddM r k'
  | EvictM_SK _ k _ k' -> Spec.EvictM k k'
  | AddB_SK _ r t j -> Spec.AddB r t j
  | EvictB_SK _ k t -> Spec.EvictB k t
  | EvictBM_SK _ k _ k' t -> Spec.EvictBM k k' t
  
let drop_slots (l:logSK) : logK 
  = map drop_slots_aux l

// likely similar to EAC: check that for every "OP s k ...", k is the last key added at slot s, and has not been evicted 
let skc (l:logSK) : Type = admit()

// add keys in a way that satisfies skc
let add_consistent_keys (l:logS) : logSK = admit()
