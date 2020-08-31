module Veritas.Verifier.Global

module MS = Veritas.MultiSet

let lemma_prefix_verifiable (gl: verifiable_log) (i:seq_index gl):
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
  if p = 0 then empty_hash_value
  else  (
    let gl' = prefix gl (p - 1) in
    lemma_prefix_verifiable gl (p - 1);
    let h1 = hadd_aux gl' in
    let h2 = VT.hadd (thread_log gl (p - 1)) in
    ms_hashfn_agg h1 h2
  )

(* aggregate hadd over all verifier threads *)
let hadd (gl: verifiable_log): ms_hash_value =
  hadd_aux gl

let rec hevict_aux (gl: verifiable_log): 
  Tot (ms_hash_value)
  (decreases (length gl)) = 
  let p = length gl in
  if p = 0 then empty_hash_value
  else  (
    let gl' = prefix gl (p - 1) in
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

(* global add sequence *)
let rec g_add_seq_aux (gl: verifiable_log): 
  Tot (seq (ms_hashfn_dom))
  (decreases (length gl)) = 
  let p = length gl in
  if p = 0 then empty #(ms_hashfn_dom)
  else (
    let gl' = prefix gl (p - 1) in
    lemma_prefix_verifiable gl (p - 1);
    append (g_add_seq_aux gl') (blum_add_seq (thread_log gl (p - 1)))
  )

(* global add sequence *)
let g_add_seq (gl: verifiable_log): seq (ms_hashfn_dom) = g_add_seq_aux gl

(* the hadd that the verifier computes is the multiset hash of all the adds *)
let rec lemma_g_hadd_correct_aux (gl: verifiable_log):
  Lemma (requires True)
        (ensures (hadd gl = ms_hashfn (g_add_seq gl)))
        (decreases (length gl)) = 
  let p = length gl in
  let s = g_add_seq gl in
  let h = hadd gl in
  
  if p = 0 then 
    lemma_hashfn_empty()
  
  else (
    let gl' = prefix gl (p - 1) in
    lemma_prefix_verifiable gl (p - 1);    
    let s' = g_add_seq gl' in
    let h' = hadd gl' in

    lemma_g_hadd_correct_aux gl';
    // assert(h' = ms_hashfn s');

    let tl = thread_log gl (p - 1) in
    let st = blum_add_seq tl in
    let ht = VT.hadd tl in
    lemma_hadd_correct tl;
    // assert(ht = ms_hashfn st);

    // assert(s == append s' st);
    // assert(h ==  ms_hashfn_agg h' ht);
    lemma_hashfn_agg s' st
  )

(* the hadd that the verifier computes is the multiset hash of all the adds *)
let lemma_g_hadd_correct (gl: verifiable_log):
  Lemma (hadd gl = ms_hashfn (g_add_seq gl)) =
  lemma_g_hadd_correct_aux gl

let rec g_evict_seq_aux (gl: verifiable_log):
  Tot (seq (ms_hashfn_dom))
  (decreases (length gl)) = 
  let p = length gl in
  if p = 0 then empty #(ms_hashfn_dom)
  else (
    let gl' = prefix gl (p - 1) in
    lemma_prefix_verifiable gl (p - 1);
    append (g_evict_seq_aux gl') (blum_evict_seq (thread_log gl (p - 1)))
  )

(* a single sequence containing all the blum evicts *)
let g_evict_seq (gl: verifiable_log): seq ms_hashfn_dom  = 
  g_evict_seq_aux gl

let rec lemma_ghevict_correct_aux (gl: verifiable_log):
  Lemma (requires True)
        (ensures (hevict gl = ms_hashfn (g_evict_seq gl)))
        (decreases (length gl)) = 
  let p = length gl in 
  let s = g_evict_seq gl in
  let h = hevict gl in

  if p = 0 then
    lemma_hashfn_empty()
  else (
    let gl' = prefix gl (p - 1) in
    lemma_prefix_verifiable gl (p - 1);
    let s' = g_evict_seq gl' in
    let h' = hevict gl' in

    lemma_ghevict_correct_aux gl';

    let tl = thread_log gl (p - 1) in
    let st = blum_evict_seq tl in
    let ht = VT.hevict tl in
    lemma_hevict_correct tl;
    
    lemma_hashfn_agg s' st
  )

let lemma_ghevict_correct (gl: verifiable_log):
  Lemma (hevict gl = ms_hashfn (g_evict_seq gl)) = 
  lemma_ghevict_correct_aux gl

let rec lemma_evict_elem_tids (gl: verifiable_log) (i: seq_index (g_evict_seq gl)):
  Lemma (MH.thread_id_of (index (g_evict_seq gl) i) < length gl) = admit()

let rec lemma_evict_elem_unique (gl: verifiable_log) (i1 i2: seq_index (g_evict_seq gl)):
  Lemma (i1 <> i2 ==> index (g_evict_seq gl) i1 <> index (g_evict_seq gl) i2) = admit()

let lemma_evict_elem_count (gl: verifiable_log) (x: ms_hashfn_dom):
  Lemma (count x (g_evict_seq gl) <= 1) = admit()

(* the global evict set is a set (not a multiset) *)
let g_evict_set_is_set (gl: verifiable_log): 
  Lemma (is_set (g_evict_set gl)) = 
  let es = g_evict_set gl in
  let aux (x:ms_hashfn_dom):
    Lemma (requires True)
          (ensures (MS.mem x es <= 1))
          [SMTPat (MS.mem x es)] = 
    lemma_evict_elem_count gl x;
    lemma_count_mem (g_evict_seq gl) x
  in
  //assert(is_set es);
  ()
