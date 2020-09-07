module Veritas.Verifier.Global

open Veritas.Interleave
open Veritas.MultiSet
open Veritas.MultiSetHash
open Veritas.Verifier
open Veritas.Verifier.Thread

open FStar.Seq
open Veritas.SeqAux

module I = Veritas.Interleave
module MH = Veritas.MultiSetHash
module V = Veritas.Verifier
module VT = Veritas.Verifier.Thread

(* Full collection of verifier logs one per thread *)
let g_vlog = seq vlog

let thread_log (gl: g_vlog) (tid: seq_index gl): thread_id_vlog = 
   (tid, index gl tid)
  
(* globally verifiable logs: every thread-level log is verifiable *)
let verifiable (gl: g_vlog) = 
  forall (tid:seq_index gl). VT.verifiable (thread_log gl tid)

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

(* global add sequence *)
val g_add_seq (gl: verifiable_log): seq (ms_hashfn_dom)

(* multiset derived from all the blum adds in gl *)
let g_add_set (gl: verifiable_log): mset ms_hashfn_dom =
  seq2mset (g_add_seq gl)

(* the hadd that the verifier computes is the multiset hash of all the adds *)
val lemma_g_hadd_correct (gl: verifiable_log):
  Lemma (hadd gl = ms_hashfn (g_add_seq gl))

(* mapping from blum_add entries in verifier log to the index in add seq *)
val add_set_map (gl: verifiable_log) (ii: sseq_index gl {is_blum_add (indexss gl ii)}):
  (j: seq_index (g_add_seq gl){index (g_add_seq gl) j = blum_add_elem (indexss gl ii)})

(* inverse mapping from add_seq to the blum add entries in the verifier logs *)
val add_set_map_inv (gl: verifiable_log) (j: seq_index (g_add_seq gl)):
  (ii: sseq_index gl {is_blum_add (indexss gl ii) /\ 
                      add_set_map gl ii = j})

val lemma_add_set_map_inv (gl: verifiable_log)(ii: sseq_index gl {is_blum_add (indexss gl ii)}):
  Lemma (requires True)
        (ensures (add_set_map_inv gl (add_set_map gl ii) = ii))
        [SMTPat (add_set_map gl ii)]

(* a single sequence containing all the blum evicts *)
val g_evict_seq (gl: verifiable_log): seq ms_hashfn_dom 

let g_evict_set (gl: verifiable_log): mset ms_hashfn_dom = 
  seq2mset (g_evict_seq gl)

val lemma_ghevict_correct (gl: verifiable_log):
  Lemma (hevict gl = ms_hashfn (g_evict_seq gl))

(* the global evict set is a set (not a multiset) *)
val g_evict_set_is_set (gl: verifiable_log): 
  Lemma (is_set (g_evict_set gl))

let blum_evict_elem (gl: verifiable_log) (ii: sseq_index gl {is_evict_to_blum (indexss gl ii)}):
  ms_hashfn_dom = 
  let (tid, i) = ii in
  let tl = thread_log gl tid in
  VT.blum_evict_elem tl i

val evict_seq_map (gl: verifiable_log) (ii: sseq_index gl {is_evict_to_blum (indexss gl ii)}):
  (j: seq_index (g_evict_seq gl) {index (g_evict_seq gl) j = 
                                  blum_evict_elem gl ii})

val evict_seq_map_inv (gl: verifiable_log) (j: seq_index (g_evict_seq gl)):
  (ii: sseq_index gl {is_evict_to_blum (indexss gl ii) /\
                      blum_evict_elem gl ii = index (g_evict_seq gl) j /\
                      evict_seq_map gl ii = j})

val lemma_evict_seq_inv (gl: verifiable_log) (ii: sseq_index gl {is_evict_to_blum (indexss gl ii)}):
  Lemma (requires True)
        (ensures (evict_seq_map_inv gl (evict_seq_map gl ii) = ii))
        [SMTPat (evict_seq_map gl ii)]
