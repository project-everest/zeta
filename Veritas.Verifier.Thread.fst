module Veritas.Verifier.Thread

let rec lemma_verifiable_implies_prefix_verifiable_aux
  (tl:verifiable_log) (i:nat{i <= length tl}):
  Lemma (requires (True))
        (ensures (verifiable (prefix tl i)))
        (decreases (length tl)) = 
  let n = length tl in
  if i = n then ()
  else lemma_verifiable_implies_prefix_verifiable_aux (prefix tl (n - 1)) i

let lemma_verifiable_implies_prefix_verifiable = lemma_verifiable_implies_prefix_verifiable_aux

(* the clock of a verifier is monotonic *)
let rec lemma_clock_monotonic_aux (tl:verifiable_log) (i:idx tl):
  Lemma (requires(True))
        (ensures (clock tl i `ts_leq` clock tl (length tl - 1)))
  (decreases (length tl))
        =
  let n = length tl in
  if n = 0 then ()
  else if i = n - 1 then ()
  else
    let tl' = prefix tl (n - 1) in
    lemma_clock_monotonic_aux tl' i

let lemma_clock_monotonic (tl: verifiable_log) (i:idx tl) (j:idx tl{j >= i}): 
  Lemma (clock tl i `ts_leq` clock tl j) = 
  let tlj = prefix tl (j + 1) in
  lemma_clock_monotonic_aux tlj i

let rec lemma_thread_id_state_aux (tl: verifiable_log):
  Lemma (requires True)
        (ensures (V.thread_id_of (verify tl) = thread_id_of tl)) 
        (decreases (length tl)) = 
  let n = length tl in
  if n = 0 then ()
  else
    lemma_thread_id_state_aux (prefix tl (n - 1))

let lemma_thread_id_state = lemma_thread_id_state_aux

let lemma_requires_key_in_store 
  (tl: verifiable_log) 
  (i:idx tl{requires_key_in_store (index tl i)}):
  Lemma (store_contains (store_idx tl i) (V.key_of (index tl i))) =
  admit()

let lemma_hadd_correct (tl: verifiable_log):
  Lemma (hadd tl = ms_hashfn (blum_add_seq tl)) = admit()


let blum_evict_elem (tl: verifiable_log) (i:idx tl{is_evict_to_blum (index tl i)}): ms_hashfn_dom =
  admit()

let blum_evict_seq (tl: verifiable_log): S.seq ms_hashfn_dom = admit()

let lemma_hevict_correct (tl: verifiable_log):
  Lemma (hevict tl = ms_hashfn (blum_evict_seq tl)) = admit()

(* all elements of tl's blum_evict_seq contain tid of tl *)
let lemma_evict_elem_tid (tl: verifiable_log):
  Lemma (all (is_of_thread_id (thread_id_of tl)) (blum_evict_seq tl)) = admit()
  
let lemma_evict_elem_unique (tl: verifiable_log) (i1 i2: SA.seq_index (blum_evict_seq tl)):
  Lemma (i1 <> i2 ==> S.index (blum_evict_seq tl) i1 <> S.index (blum_evict_seq tl) i2) = admit()
