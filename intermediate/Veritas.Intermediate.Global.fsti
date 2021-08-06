module Veritas.Intermediate.Global

open FStar.Seq
open Veritas.MultiSet
open Veritas.MultiSetHash
open Veritas.MultiSetHashDomain
open Veritas.SeqAux
open Veritas.Interleave
open Veritas.Intermediate.Logs
open Veritas.Intermediate.Thread

module S = FStar.Seq
module SA = Veritas.SeqAux
module IntLog = Veritas.Intermediate.Logs
module IntT = Veritas.Intermediate.Thread

let g_logS vcfg = seq (logS vcfg)

let thread_log #vcfg (gl:g_logS vcfg) (tid:SA.seq_index gl): thread_id_logS _ = 
   (tid, Seq.index gl tid)

let to_state_ops #vcfg (gl:g_logS vcfg) =
  map IntLog.to_state_ops gl

let verifiable #vcfg (gl: g_logS vcfg) = 
  forall (tid:SA.seq_index gl). {:pattern IntT.verify (thread_log gl tid)} IntT.verifiable (thread_log gl tid)

let verifiable_log vcfg = gl:g_logS vcfg{verifiable gl}

val verifiable_implies_prefix_verifiable
  (#vcfg:_) (gl:verifiable_log vcfg) (i:nat{i <= Seq.length gl}):
  Lemma (ensures (verifiable #vcfg (SA.prefix gl i)))
        [SMTPat (SA.prefix gl i)]

let rec hadd_aux #vcfg (gl: verifiable_log vcfg) (ep: epoch):
  Tot (ms_hash_value)
  (decreases (S.length gl)) = 
  let p = S.length gl in
  if p = 0 then empty_hash_value
  else  (
    let gl' = SA.prefix gl (p - 1) in
    let h1 = hadd_aux gl' ep in
    let h2 = IntT.hadd (thread_log gl (p - 1)) ep in
    ms_hashfn_agg h1 h2
  )

let hadd #vcfg (gl: verifiable_log vcfg) (ep: epoch): ms_hash_value =
  hadd_aux gl ep

let rec hevict_aux #vcfg (gl: verifiable_log vcfg) (ep: epoch):
  Tot (ms_hash_value)
  (decreases (S.length gl)) = 
  let p = S.length gl in
  if p = 0 then empty_hash_value
  else  (
    let gl' = SA.prefix gl (p - 1) in
    let h1 = hevict_aux gl' ep in
    let h2 = IntT.hevict (thread_log gl (p - 1)) ep in
    ms_hashfn_agg h1 h2
  )

let hevict (#vcfg:_) (gl: verifiable_log vcfg) (ep: epoch): ms_hash_value = hevict_aux gl ep

let hash_verifiable_epoch #vcfg (gl: verifiable_log vcfg) (ep: epoch) =
  hadd gl ep = hevict gl ep

let hash_verifiable_prop #vcfg (gl: verifiable_log vcfg) (epmax: epoch) (ep: epoch) =
  ep <= epmax ==> hash_verifiable_epoch gl ep

let hash_verifiable #vcfg (epmax: epoch) (gl: verifiable_log vcfg) =
  forall (ep: epoch). {:pattern hash_verifiable_prop gl epmax ep} hash_verifiable_prop gl epmax ep

let hash_verifiable_log vcfg (ep: epoch) = gl:verifiable_log vcfg{hash_verifiable ep gl}

/// the the clock of a specific log entry
/// 
let clock #vcfg (gl: verifiable_log vcfg) (i: sseq_index gl): timestamp = 
  let (tid, idx) = i in  
  let tl = thread_log gl tid in
  IntT.clock tl idx

(* global add sequence *)
val add_seq (#vcfg:_) (ep: epoch) (gl: verifiable_log vcfg): seq (ms_hashfn_dom)

(* multiset derived from all the blum adds in gl *)
let add_set (#vcfg) (ep: epoch) (gl: verifiable_log vcfg): mset_ms_hashfn_dom =
  seq2mset #_ #ms_hashfn_dom_cmp (add_seq ep gl)

///  the hadd that the verifier computes is the multiset hash of all the adds
val lemma_g_hadd_correct (#vcfg:_) (ep: epoch) (gl: verifiable_log vcfg):
  Lemma (ensures (hadd gl ep = ms_hashfn (add_seq ep gl)))

(* mapping from blum_add entries in verifier log to the index in add seq *)
val add_set_map (#vcfg:_) (gl: verifiable_log vcfg) (ii: sseq_index gl {is_blum_add (indexss gl ii)}):
  (let e = indexss gl ii in
   let be = blum_add_elem e in
   let ep = epoch_of be in
   let as = add_seq ep gl in
   j: SA.seq_index as {S.index as j = be})

(* inverse mapping from add_seq to the blum add entries in the verifier logs *)
val add_set_map_inv (#vcfg:_) (ep: epoch) (gl: verifiable_log vcfg) (j: SA.seq_index (add_seq ep gl)):
  (ii: sseq_index gl {let e = indexss gl ii in
                      is_blum_add e /\
                      (let be = blum_add_elem e in
                       let as = add_seq ep gl in
                       be = S.index as j /\
                       add_set_map gl ii = j /\
                       ep = epoch_of be)})

val lemma_add_set_map_inv (#vcfg:_) (gl: verifiable_log vcfg) (ii: sseq_index gl {is_blum_add (indexss gl ii)}):
  Lemma (ensures (let e = indexss gl ii in
                  let be = blum_add_elem e in
                  let ep = epoch_of be in
                  let j = add_set_map gl ii in
                  add_set_map_inv ep gl j = ii))
        [SMTPat (add_set_map gl ii)]

(* a single sequence containing all the blum evicts *)
val evict_seq (#vcfg:_) (ep: epoch) (gl: verifiable_log vcfg): seq ms_hashfn_dom

let evict_set (#vcfg:_) (ep: epoch) (gl: verifiable_log vcfg): mset_ms_hashfn_dom =
  seq2mset #_ #ms_hashfn_dom_cmp (evict_seq ep gl)

val lemma_ghevict_correct (#vcfg:_) (ep: epoch) (gl: verifiable_log vcfg):
  Lemma (ensures (hevict gl ep = ms_hashfn (evict_seq ep gl)))

(* the global evict set is a set (not a multiset) *)
val evict_set_is_set (#vcfg:_) (ep: epoch) (gl: verifiable_log vcfg):
  Lemma (ensures (is_set (evict_set ep gl)))

let blum_evict_elem (#vcfg:_) (gl: verifiable_log vcfg) (ii: sseq_index gl {is_evict_to_blum (indexss gl ii)}):
  ms_hashfn_dom = 
  let (tid, i) = ii in
  let tl = thread_log gl tid in
  IntT.blum_evict_elem tl i

val evict_seq_map (#vcfg:_) (gl: verifiable_log vcfg) (ii: sseq_index gl {is_evict_to_blum (indexss gl ii)}):
  (let e = indexss gl ii in
   let be = blum_evict_elem gl ii in
   let ep = epoch_of be in
   let es = evict_seq ep gl in
   j: SA.seq_index es {S.index es j = be})

val evict_seq_map_inv (#vcfg:_) (ep: epoch) (gl: verifiable_log vcfg) (j: SA.seq_index (evict_seq ep gl)):
  (ii: sseq_index gl {let e = indexss gl ii in
                      is_evict_to_blum e /\
                      (let be = blum_evict_elem gl ii in
                       let es = evict_seq ep gl in
                       be = S.index es j /\
                       ep = epoch_of be /\
                       evict_seq_map gl ii = j)})

val lemma_evict_seq_inv (#vcfg:_) (gl: verifiable_log vcfg) (ii: sseq_index gl {is_evict_to_blum (indexss gl ii)}):
  Lemma (ensures (let e = indexss gl ii in
                  let be = blum_evict_elem gl ii in
                  let ep = epoch_of be in
                  let j = evict_seq_map gl ii in
                  evict_seq_map_inv ep gl j = ii))

val hadd_hevict_equal (#vcfg:_) (epmax: epoch) (gl: hash_verifiable_log vcfg epmax) (ep: epoch{ep <= epmax}):
  Lemma (ensures (hadd gl ep = hevict gl ep /\
                  ms_hashfn (add_seq ep gl) = ms_hashfn (evict_seq ep gl)))

val prefix_upto_epoch (#vcfg:_) (ep: epoch) (gl: verifiable_log vcfg)
  : (gl': verifiable_log vcfg {S.length gl = S.length gl' })

val lemma_prefix_upto_epoch (#vcfg:_) (ep: epoch) (gl: verifiable_log vcfg) (tid: SA.seq_index gl):
  Lemma (ensures (let tl = thread_log gl tid in
                  let _, l_ep = IntT.prefix_upto_epoch ep tl in
                  let gl_ep = prefix_upto_epoch ep gl in
                  l_ep = S.index gl_ep tid))
