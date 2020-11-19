
module Veritas.Intermediate.Logs

open Veritas.Key
open Veritas.MultiSetHashDomain
open Veritas.Record
open Veritas.SeqAux

module Spec = Veritas.Verifier

let slot_id = nat
let thread_id = Spec.thread_id

(* Definitions of different styles of verifier logs.
   - logK : contains only key references (defined in Veritas.Verifier)
   - logS: contains slot references
   - logL: contains slot references & low-level data structures (TODO) *)

let logK_entry = Spec.vlog_entry
let logK = Spec.vlog

type logS_entry =
  | Get_S: s:slot_id -> k:data_key -> v:data_value -> logS_entry
  | Put_S: s:slot_id -> k:data_key -> v:data_value -> logS_entry
  | AddM_S: s:slot_id -> r:record -> s':slot_id -> logS_entry
  | EvictM_S: s:slot_id -> s':slot_id -> logS_entry
  | AddB_S: s:slot_id -> r:record -> t:timestamp -> j:thread_id -> logS_entry
  | EvictB_S: s:slot_id -> t:timestamp -> logS_entry
  | EvictBM_S: s:slot_id -> s':slot_id -> t:timestamp -> logS_entry
             
let logS = Seq.seq logS_entry

let is_state_op (e: logS_entry): bool =
  match e with
  | Get_S _ _ _ | Put_S _ _ _ -> true
  | _ -> false

let to_state_op (e:logS_entry {is_state_op e}): Veritas.State.state_op =
  match e with
  | Get_S _ k v -> Veritas.State.Get k v
  | Put_S _ k v -> Veritas.State.Put k v

let to_state_op_logS (l: logS) =
  map to_state_op (filter_refine is_state_op l)

let thread_id_logS = thread_id & logS

let g_logS = Seq.seq logS

let thread_log (gl: g_logS) (tid: seq_index gl): thread_id_logS = 
   (tid, Seq.index gl tid)

let to_state_op_glogS (gl: g_logS) =
  map to_state_op_logS gl
