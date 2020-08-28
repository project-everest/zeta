module Veritas.Verifier.Global

open Veritas.Interleave
open Veritas.MultiSetHash
open Veritas.Verifier
open Veritas.Verifier.Thread

open FStar.Seq
open Veritas.SeqAux

module MH = Veritas.MultiSetHash
module V = Veritas.Verifier
module VT = Veritas.Verifier.Thread

(* Full collection of verifier logs one per thread *)
let g_vlog = (gl:seq vlog{length gl > 0})

let thread_log (gl: g_vlog) (tid: seq_index gl): thread_id_vlog = 
   (tid, index gl tid)
  
(* globally verifiable logs: every thread-level log is verifiable *)
let verifiable (gl: g_vlog) = 
  forall (tid:seq_index gl). {:pattern (thread_log gl tid)} VT.verifiable (thread_log gl tid)

(* Refinement type of logs that are verifiable *)
let verifiable_log = gl:g_vlog{verifiable gl}

(* add-set hash over all verifier threads *)
val hadd (gl: verifiable_log): ms_hash_value

(* hash of evict set over all verifier threads *)
val hevict (gl: verifiable_log): ms_hash_value

(* a verifiable log is hash verifiable if add and evict set hashes are equal *)
let hash_verifiable (gl: verifiable_log): bool = 
  hadd gl = hevict gl

let hash_verifiable_log = gl:verifiable_log{hash_verifiable gl}

(* 
 * return the clock of a particular log entry. the index i here 
 * is a pair that identifies the verifier thread and an entry
 * in the thread log
 *)
val clock (gl: verifiable_log) (i: sseq_index gl): timestamp

(* time ordered interleaving of a verifier logs. the "constructor" of the 
 * interleaving contains both the sequence and the proof of the interleaving
 * which helps track the lineage of each entry in the interleaved sequence *)
val time_seq_ctor (gl: verifiable_log): (interleave_ctor gl)

