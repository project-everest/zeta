module Veritas.Verifier.Global

let lemma_prefix_verifiable (gl: verifiable_log) (i:seq_index gl{i > 0}):
  Lemma (verifiable (prefix gl i)) = 
  let pgl = prefix gl i in
  let aux (tid:seq_index pgl):
    Lemma (requires True)
          (ensures (VT.verifiable (thread_log pgl tid)))
          [SMTPat (VT.verifiable (thread_log pgl tid))] = 
    assert(thread_log pgl tid = thread_log gl tid);
    ()
  in
  ()

let rec hadd_aux (gl: verifiable_log): 
  Tot (ms_hash_value)
  (decreases (length gl)) = 
  let p = length gl in
  if p = 1 then 
    thread_hadd (VT.verify (thread_log gl 0))  
  else  (
    let gl': g_vlog = prefix gl (p - 1) in
    lemma_prefix_verifiable gl (p - 1);
    let h1 = hadd_aux gl' in
    let h2 = thread_hadd (VT.verify (thread_log gl (p - 1))) in
    ms_hashfn_agg h1 h2
  )

(* aggregate hadd over all verifier threads *)
let hadd (gl: verifiable_log): ms_hash_value =
  hadd_aux gl

let rec hevict_aux (gl: verifiable_log): 
  Tot (ms_hash_value)
  (decreases (length gl)) = 
  let p = length gl in
  if p = 1 then 
    thread_hevict (VT.verify (thread_log gl 0))  
  else  (
    let gl': g_vlog = prefix gl (p - 1) in
    lemma_prefix_verifiable gl (p - 1);
    let h1 = hevict_aux gl' in
    let h2 = thread_hevict (VT.verify (thread_log gl (p - 1))) in
    ms_hashfn_agg h1 h2
  )

(* aggregate hadd over all verifier threads *)
let hevict (gl: verifiable_log): ms_hash_value =
  hevict_aux gl

let clock (gl: verifiable_log) (i: sseq_index gl): timestamp = 
  let (tid, idx) = i in  
  let tl = thread_log gl tid in
  VT.clock tl idx

let time_seq_ctor (gl: verifiable_log): (interleave_ctor gl) = admit()

