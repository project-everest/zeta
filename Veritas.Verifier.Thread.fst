module Veritas.Verifier.Thread

module MH = Veritas.MultiSetHash

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

let lemma_state_transition (tl: verifiable_log) (i: idx tl):
  Lemma (state_at tl (i + 1) ==
         t_verify_step (state_at tl i) (index tl i)) = 
  ()

let lemma_requires_key_in_store
  (tl: verifiable_log)
  (i:idx tl{requires_key_in_store (index tl i)}):
  Lemma (store_contains (store_at tl i) (V.key_of (index tl i))) =
  lemma_verifiable_implies_prefix_verifiable tl (i + 1)

let rec blum_add_seq_aux (tl: verifiable_log):
  Tot (S.seq ms_hashfn_dom)
  (decreases (length tl)) =
  let n = length tl in
  if n = 0 then S.empty #ms_hashfn_dom
  else
    let tl' = prefix tl (n - 1) in
    let s' = blum_add_seq_aux tl' in
    let e = index tl (n - 1) in
    if is_blum_add e then SA.append1 s' (blum_add_elem e)
    else s'

let blum_add_seq = blum_add_seq_aux

let hadd_at (tl: verifiable_log) (i:nat{i <= length tl}): ms_hash_value =
  Valid?.hadd (state_at tl i)

let lemma_hadd_unchanged (tl: verifiable_log) (i: idx tl{not (is_blum_add (index tl i))}):
  Lemma (hadd_at tl i == hadd_at tl (i + 1)) = 
  lemma_state_transition tl i;
  ()

let rec lemma_hadd_correct_aux (tl: verifiable_log):
  Lemma (requires True)
        (ensures (hadd tl = ms_hashfn (blum_add_seq tl)))
        (decreases (length tl)) =
  let n = length tl in
  if n = 0 then
    lemma_hashfn_empty()
  else (
    let tl' = prefix tl (n - 1) in
    let s' = blum_add_seq tl' in
    let e = index tl (n - 1) in
    let h' = hadd tl' in
    lemma_hadd_correct_aux tl';
    if is_blum_add e then lemma_hashfn_app s' (blum_add_elem e)      
    else lemma_hadd_unchanged tl (n - 1)      
  )

let lemma_hadd_correct = lemma_hadd_correct_aux

let blum_evict_elem (tl: verifiable_log) (i:idx tl{is_evict_to_blum (index tl i)}): ms_hashfn_dom =
  let tli = prefix tl i in
  let tli' = prefix tl (i + 1) in
  let e = index tl i in
  match e with
  | EvictB k t -> 
    let st = store_at tl i in
    let v = stored_value st k in
    MHDom (k,v) t (thread_id_of tl) 
  | EvictBM k k' t -> 
    let st = store_at tl i in
    let v = stored_value st k in
    MHDom (k,v) t (thread_id_of tl)   

let rec blum_evict_seq_aux (tl: verifiable_log): 
  Tot (S.seq ms_hashfn_dom)
  (decreases (length tl)) = 
  let n = length tl in
  if n = 0 then S.empty #ms_hashfn_dom
  else (
    let tl' = prefix tl (n - 1) in
    let s' = blum_evict_seq_aux tl' in
    let e = index tl (n - 1) in
    if is_evict_to_blum e then
      SA.append1 s' (blum_evict_elem tl (n - 1))
    else s'
  )

let blum_evict_seq (tl: verifiable_log): S.seq ms_hashfn_dom = 
  blum_evict_seq_aux tl

let hevict_at (tl: verifiable_log) (i:nat{i <= length tl}): ms_hash_value =
  Valid?.hevict (state_at tl i)

let lemma_hevict_unchanged (tl:verifiable_log) (i:idx tl{not (is_evict_to_blum (index tl i))}):
  Lemma (hevict_at tl i = hevict_at tl (i + 1)) = ()

let lemma_hevict_change (tl: verifiable_log) (i: idx tl{is_evict_to_blum (index tl i)}):
  Lemma (hevict_at tl (i + 1) = ms_hashfn_upd (blum_evict_elem tl i) (hevict_at tl i)) = 
  lemma_state_transition tl i;
  lemma_thread_id_state (prefix tl i);  
  ()

let rec lemma_hevict_correct_aux (tl: verifiable_log):
  Lemma (requires True)
        (ensures (hevict tl = ms_hashfn (blum_evict_seq tl)))
        (decreases (length tl)) = 
  let n = length tl in
  if n = 0 then 
    lemma_hashfn_empty()
  else (
    let tl' = prefix tl (n - 1) in
    let s' = blum_evict_seq tl' in
    let e = index tl (n - 1) in
    let h' = hevict tl' in
    lemma_hevict_correct_aux tl';
    if is_evict_to_blum e then (
      lemma_hashfn_app s' (blum_evict_elem tl (n - 1));
      lemma_hevict_change tl (n - 1)
    )
    else 
      lemma_hevict_unchanged tl (n - 1)    
  )


let lemma_hevict_correct (tl: verifiable_log):
  Lemma (hevict tl = ms_hashfn (blum_evict_seq tl)) = 
  lemma_hevict_correct_aux tl

(* all elements of tl's blum_evict_seq contain tid of tl *)
let rec lemma_evict_elem_tid_aux (tl: verifiable_log) (i: SA.seq_index (blum_evict_seq tl)):
  Lemma (requires True)
        (ensures (MH.thread_id_of (S.index (blum_evict_seq tl) i) = (thread_id_of tl))) 
        (decreases (length tl))
        [SMTPat (is_of_thread_id (thread_id_of tl) (S.index (blum_evict_seq tl) i))] = 
  let es = blum_evict_seq tl in
  let tid = thread_id_of tl in
  let n = length tl in
  if n = 0 then ()
  else (
    let tl' = prefix tl (n - 1) in
    let es' = blum_evict_seq tl' in
    let e = index tl (n - 1) in
    if is_evict_to_blum e then (
      //assert(es == SA.append1 es' (blum_evict_elem tl (n - 1)));
      if i = S.length es - 1 then (
        //assert(S.index es i = (blum_evict_elem tl (n - 1)));        
        ()
      )
      else (
        //assert(S.index es i = S.index es' i);
        lemma_evict_elem_tid_aux tl' i
      )
    )
    else lemma_evict_elem_tid_aux tl' i    
  )

let lemma_evict_elem_tid (tl: verifiable_log):
  Lemma (all (is_of_thread_id (thread_id_of tl)) (blum_evict_seq tl)) = ()

let clock_pre (tl:verifiable_log) (i:idx tl): timestamp = 
  Valid?.clk (state_at tl i)

let lemma_evict_clock_strictly_increasing (tl: verifiable_log) (i: idx tl {is_evict_to_blum (index tl i)}):
  Lemma (ts_lt (clock_pre tl i) (clock tl i)) = admit()

let lemma_evict_timestamp_is_clock (tl: verifiable_log) (i: idx tl{is_evict_to_blum (index tl i)}):
  Lemma (timestamp_of (blum_evict_elem tl i) = clock tl i) = admit()

let rec lemma_evict_seq_clock_strictly_monotonic (tl: verifiable_log) (i1 i2: SA.seq_index (blum_evict_seq tl)):
  Lemma (requires (i1 < i2))
        (ensures (ts_lt (timestamp_of (S.index (blum_evict_seq tl) i1)) 
                        (timestamp_of (S.index (blum_evict_seq tl) i2)))) 
        (decreases (length tl)) =
  let n = length tl in
  let es = blum_evict_seq tl in
  if n = 0 then ()
  else (
    let tl' = prefix tl (n - 1) in
    let es' = blum_evict_seq tl' in
    if i2 < S.length es' then
      lemma_evict_seq_clock_strictly_monotonic tl' i1 i2
    else (
      let e = index tl (n - 1) in
      assert(is_evict_to_blum e);
      
      admit()
    )
  )

let lemma_evict_elem_unique (tl: verifiable_log) (i1 i2: SA.seq_index (blum_evict_seq tl)):
  Lemma (i1 <> i2 ==> S.index (blum_evict_seq tl) i1 <> S.index (blum_evict_seq tl) i2) = 
  if i1 = i2 then ()
  else if i1 < i2 then
    lemma_evict_seq_clock_strictly_monotonic tl i1 i2
  else 
    lemma_evict_seq_clock_strictly_monotonic tl i2 i1
   
