module Veritas.Intermediate.Common
open Veritas.Record

type slot_id = nat

let key = Veritas.Key.key
let value = Veritas.Record.value
let data_value = Veritas.Record.data_value 
let add_method = Veritas.Verifier.add_method

(* KH: too high-level to require value_of_type_k? does this add runtime overhead
   in extracted code? *)
type record = 
  | Record: k:key -> v:value_type_of k -> am:add_method -> record

let thread_id = Veritas.Verifier.thread_id
let timestamp = Veritas.MultiSetHashDomain.timestamp

noeq
type vlog_entry =
  | Get:     s:slot_id ->
             v:data_value ->
             vlog_entry
  | Put:     s:slot_id ->
             v:data_value ->
             vlog_entry
  | AddM:    s:slot_id ->
             r:record ->
             s':slot_id ->
             vlog_entry
  | EvictM:  s:slot_id ->
             s':slot_id ->
             vlog_entry
  | AddB:    s:slot_id ->
             r:record ->
             t:timestamp ->
             j:thread_id ->
             vlog_entry
  | EvictB:  s:slot_id ->
             t:timestamp ->
             vlog_entry
  | EvictBM: s:slot_id ->
             s':slot_id ->
             t:timestamp ->
             vlog_entry
