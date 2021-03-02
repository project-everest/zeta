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

let rec hadd_aux #vcfg (gl: verifiable_log vcfg): 
  Tot (ms_hash_value)
  (decreases (S.length gl)) = 
  let p = S.length gl in
  if p = 0 then empty_hash_value
  else  (
    let gl' = SA.prefix gl (p - 1) in
    let h1 = hadd_aux gl' in
    let h2 = IntT.hadd (thread_log gl (p - 1)) in
    ms_hashfn_agg h1 h2
  )

let hadd #vcfg (gl: verifiable_log vcfg): ms_hash_value = 
  hadd_aux gl

let rec hevict_aux #vcfg (gl: verifiable_log vcfg): 
  Tot (ms_hash_value)
  (decreases (S.length gl)) = 
  let p = S.length gl in
  if p = 0 then empty_hash_value
  else  (
    let gl' = SA.prefix gl (p - 1) in
    let h1 = hevict_aux gl' in
    let h2 = IntT.hevict (thread_log gl (p - 1)) in
    ms_hashfn_agg h1 h2
  )

let hevict (#vcfg:_) (gl: verifiable_log vcfg): ms_hash_value = hevict_aux gl

let hash_verifiable #vcfg (gl: verifiable_log vcfg): bool = 
  hadd gl = hevict gl

let hash_verifiable_log vcfg = gl:verifiable_log vcfg{hash_verifiable gl}

/// the the clock of a specific log entry
/// 
let clock #vcfg (gl: verifiable_log vcfg) (i: sseq_index gl): timestamp = 
  let (tid, idx) = i in  
  let tl = thread_log gl tid in
  IntT.clock tl idx

(* global add sequence *)
val add_seq (#vcfg:_) (gl: verifiable_log vcfg): seq (ms_hashfn_dom)

(* multiset derived from all the blum adds in gl *)
let add_set (#vcfg) (gl: verifiable_log vcfg): mset_ms_hashfn_dom =
  seq2mset #_ #ms_hashfn_dom_cmp (add_seq gl)

///  the hadd that the verifier computes is the multiset hash of all the adds
val lemma_g_hadd_correct (#vcfg:_) (gl: verifiable_log vcfg):
  Lemma (ensures (hadd gl = ms_hashfn (add_seq gl)))
        [SMTPat (verifiable gl)]

(* mapping from blum_add entries in verifier log to the index in add seq *)
val add_set_map (#vcfg:_) (gl: verifiable_log vcfg) (ii: sseq_index gl {is_blum_add (indexss gl ii)}):
  (j: SA.seq_index (add_seq gl){S.index (add_seq gl) j = blum_add_elem (indexss gl ii)})

(* inverse mapping from add_seq to the blum add entries in the verifier logs *)
val add_set_map_inv (#vcfg:_) (gl: verifiable_log vcfg) (j: SA.seq_index (add_seq gl)):
  (ii: sseq_index gl {is_blum_add (indexss gl ii) /\ 
                      add_set_map gl ii = j})

val lemma_add_set_map_inv (#vcfg:_) (gl: verifiable_log vcfg) (ii: sseq_index gl {is_blum_add (indexss gl ii)}):
  Lemma (ensures (add_set_map_inv gl (add_set_map gl ii) = ii))
        [SMTPat (add_set_map gl ii)]

(* a single sequence containing all the blum evicts *)
val evict_seq (#vcfg:_) (gl: verifiable_log vcfg): seq ms_hashfn_dom 

let evict_set (#vcfg:_) (gl: verifiable_log vcfg): mset_ms_hashfn_dom = 
  seq2mset #_ #ms_hashfn_dom_cmp (evict_seq gl)

val lemma_ghevict_correct (#vcfg:_) (gl: verifiable_log vcfg):
  Lemma (ensures (hevict gl = ms_hashfn (evict_seq gl)))
        [SMTPat (verifiable gl)]

(* the global evict set is a set (not a multiset) *)
val evict_set_is_set (#vcfg:_) (gl: verifiable_log vcfg): 
  Lemma (ensures (is_set (evict_set gl)))
        [SMTPat (verifiable gl)]

let blum_evict_elem (#vcfg:_) (gl: verifiable_log vcfg) (ii: sseq_index gl {is_evict_to_blum (indexss gl ii)}):
  ms_hashfn_dom = 
  let (tid, i) = ii in
  let tl = thread_log gl tid in
  IntT.blum_evict_elem tl i

val evict_seq_map (#vcfg:_) (gl: verifiable_log vcfg) (ii: sseq_index gl {is_evict_to_blum (indexss gl ii)}):
  (j: SA.seq_index (evict_seq gl) {S.index (evict_seq gl) j = 
                                  blum_evict_elem gl ii})

val evict_seq_map_inv (#vcfg:_) (gl: verifiable_log vcfg) (j: SA.seq_index (evict_seq gl)):
  (ii: sseq_index gl {is_evict_to_blum (indexss gl ii) /\
                      blum_evict_elem gl ii = S.index (evict_seq gl) j /\
                      evict_seq_map gl ii = j})

val lemma_evict_seq_inv (#vcfg:_) (gl: verifiable_log vcfg) (ii: sseq_index gl {is_evict_to_blum (indexss gl ii)}):
  Lemma (requires True)
        (ensures (evict_seq_map_inv gl (evict_seq_map gl ii) = ii))
        [SMTPat (evict_seq_map gl ii)]
