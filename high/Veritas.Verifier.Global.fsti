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

val lemma_prefix_verifiable (gl: verifiable_log) (i:seq_index gl):
  Lemma (ensures (verifiable (prefix gl i)))
        [SMTPat (prefix gl i)]

let rec hadd_aux (gl: verifiable_log) (ep: epoch):
  Tot (ms_hash_value)
  (decreases (length gl)) = 
  let p = length gl in
  if p = 0 then empty_hash_value
  else  (
    let gl' = prefix gl (p - 1) in
    let h1 = hadd_aux gl' ep in
    let h2 = VT.hadd (thread_log gl (p - 1)) ep in
    ms_hashfn_agg h1 h2
  )

(* add-set hash over all verifier threads *)
let hadd (gl: verifiable_log) (ep: epoch): ms_hash_value =
  hadd_aux gl ep

let rec hevict_aux (gl: verifiable_log) (ep: epoch):
  Tot (ms_hash_value)
  (decreases (length gl)) = 
  let p = length gl in
  if p = 0 then empty_hash_value
  else  (
    let gl' = prefix gl (p - 1) in
    let h1 = hevict_aux gl' ep in
    let h2 = thread_hevict (VT.verify (thread_log gl (p - 1))) ep in
    ms_hashfn_agg h1 h2
  )

(* hash of evict set over all verifier threads *)
let hevict (gl: verifiable_log) (ep: epoch): ms_hash_value =
  hevict_aux gl ep

(* add and evict sets are equal for a specified epoch *)
let hash_verifiable_epoch (gl: verifiable_log) (ep: epoch) =
  hadd gl ep = hevict gl ep

let hash_verifiable_prop (gl: verifiable_log) (epmax: epoch) (ep: epoch) =
  ep <= epmax ==> hash_verifiable_epoch gl ep

(* a verifiable log is hash verifiable if add and evict set hashes are equal *)
let hash_verifiable (epmax: epoch) (gl: verifiable_log) =
  forall ep. {:pattern hash_verifiable_prop gl epmax ep} hash_verifiable_prop gl epmax ep

(* hash verifiable upto epoch ep *)
let hash_verifiable_log (ep: epoch) = gl:verifiable_log{hash_verifiable ep gl}

val hadd_hevict_equal (epmax: epoch) (gl: hash_verifiable_log epmax) (ep: epoch{ep <= epmax}):
  Lemma (ensures (hadd gl ep = hevict gl ep))

(* 
 * return the clock of a particular log entry. the index i here 
 * is a pair that identifies the verifier thread and an entry
 * in the thread log
 *)
 
//val clock (gl: verifiable_log) (i: sseq_index gl): timestamp

let clock (gl: verifiable_log) (i: sseq_index gl): timestamp = 
  let (tid, idx) = i in  
  let tl = thread_log gl tid in
  VT.clock tl idx

(* global add sequence *)
val g_add_seq (ep: epoch) (gl: verifiable_log): seq (ms_hashfn_dom)

(* multiset derived from all the blum adds in gl *)
let g_add_set (ep: epoch) (gl: verifiable_log): mset_ms_hashfn_dom =
  seq2mset #_ #ms_hashfn_dom_cmp (g_add_seq ep gl)

(* the hadd that the verifier computes is the multiset hash of all the adds *)
val lemma_g_hadd_correct (ep: epoch) (gl: verifiable_log):
  Lemma (hadd gl ep = ms_hashfn (g_add_seq ep gl))

(* mapping from blum_add entries in verifier log to the index in add seq of the epoch *)
val add_set_map (gl: verifiable_log) (ii: sseq_index gl {is_blum_add (indexss gl ii)}):
  (let e = indexss gl ii in
   let be = blum_add_elem e in
   let ep = epoch_of be in
   let add_seq = g_add_seq ep gl in
   j: seq_index add_seq {index add_seq j = be})

(* inverse mapping from add_seq to the blum add entries in the verifier logs *)
val add_set_map_inv (ep: epoch) (gl: verifiable_log) (j: seq_index (g_add_seq ep gl)):
  (ii: sseq_index gl {let e = indexss gl ii in
                      is_blum_add e /\
                      (let be = blum_add_elem e in
                       let add_seq = g_add_seq ep gl in
                       be = index add_seq j /\
                       add_set_map gl ii = j /\
                       ep = epoch_of be)})

val lemma_add_set_map_inv (gl: verifiable_log)(ii: sseq_index gl {is_blum_add (indexss gl ii)}):
  Lemma (ensures (let e = indexss gl ii in
                  let be = blum_add_elem e in
                  let ep = epoch_of be in
                  let j = add_set_map gl ii in
                  add_set_map_inv ep gl j = ii))
        [SMTPat (add_set_map gl ii)]

(* a single sequence containing all the blum evicts *)
val g_evict_seq (ep: epoch) (gl: verifiable_log): seq ms_hashfn_dom

let g_evict_set (ep: epoch) (gl: verifiable_log): mset_ms_hashfn_dom =
  seq2mset #_ #ms_hashfn_dom_cmp (g_evict_seq ep gl)

val lemma_ghevict_correct (ep: epoch) (gl: verifiable_log):
  Lemma (hevict gl ep = ms_hashfn (g_evict_seq ep gl))

(* the global evict set is a set (not a multiset) *)
val g_evict_set_is_set (ep: epoch) (gl: verifiable_log):
  Lemma (is_set (g_evict_set ep gl))

let blum_evict_elem (gl: verifiable_log) (ii: sseq_index gl {is_evict_to_blum (indexss gl ii)}):
  ms_hashfn_dom = 
  let (tid, i) = ii in
  let tl = thread_log gl tid in
  VT.blum_evict_elem tl i

val evict_seq_map (gl: verifiable_log) (ii: sseq_index gl {is_evict_to_blum (indexss gl ii)}):
  (let e = indexss gl ii in
   let be = blum_evict_elem gl ii in
   let ep = epoch_of be in
   let evict_seq = g_evict_seq ep gl in

   j: seq_index evict_seq {index evict_seq j = be})

val evict_seq_map_inv (ep: epoch) (gl: verifiable_log) (j: seq_index (g_evict_seq ep gl)):
  (ii: sseq_index gl {let e = indexss gl ii in
                      is_evict_to_blum e /\
                      (let be = blum_evict_elem gl ii in
                       let evict_seq = g_evict_seq ep gl in
                       be = index evict_seq j /\
                       evict_seq_map gl ii = j /\
                       ep = epoch_of be)})

val lemma_evict_seq_inv (gl: verifiable_log) (ii: sseq_index gl {is_evict_to_blum (indexss gl ii)}):
  Lemma (ensures (let e = indexss gl ii in
                  let be = blum_evict_elem gl ii in
                  let ep = epoch_of be in
                  let j = evict_seq_map gl ii in
                  evict_seq_map_inv ep gl j = ii))
        [SMTPat (evict_seq_map gl ii)]

val prefix_upto_epoch (ep: epoch) (gl: verifiable_log): (gl': verifiable_log { length gl' = length gl })

val lemma_prefix_upto_epoch (ep: epoch) (gl: verifiable_log) (tid: seq_index gl):
  Lemma (ensures (let tl = thread_log gl tid in
                  let _, l_ep = VT.prefix_upto_epoch ep tl in
                  let gl_ep = prefix_upto_epoch ep gl in
                  l_ep = index gl_ep tid))
