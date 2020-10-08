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

#push-options "--z3rlimit_factor 3"
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
#pop-options

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

let rec add_seq_map_aux (tl: verifiable_log) (i: idx tl{is_blum_add (index tl i)}):
  Tot (j: SA.seq_index (blum_add_seq tl){S.index (blum_add_seq tl) j =
                                         blum_add_elem (index tl i)})
  (decreases (length tl)) = 
  let n = length tl in                                     
  if n = 0 then 0
  else
    let tl' = prefix tl (n - 1) in
    let s' = blum_add_seq tl' in
    if i = n - 1 then
      S.length s'
    else
      add_seq_map_aux tl' i    
  
let add_seq_map (tl: verifiable_log) (i: idx tl{is_blum_add (index tl i)}):
  (j: SA.seq_index (blum_add_seq tl){S.index (blum_add_seq tl) j =
                                     blum_add_elem (index tl i)}) = 
  add_seq_map_aux tl i                                     

let rec add_seq_map_inv_aux (tl: verifiable_log) (j: SA.seq_index (blum_add_seq tl)):
  Tot (i: idx tl {is_blum_add (index tl i) /\
                  blum_add_elem (index tl i) = S.index (blum_add_seq tl) j /\
                  add_seq_map tl i = j})
  (decreases (length tl)) = 
  let n = length tl in
  if n = 0 then 0
  else
    let tl' = prefix tl (n - 1) in
    let s' = blum_add_seq_aux tl' in
    let e = index tl (n - 1) in
    let s = blum_add_seq tl in
    if j = S.length s' then 
      n - 1
    else
      add_seq_map_inv_aux tl' j

let add_seq_inv_map (tl: verifiable_log) (j: SA.seq_index (blum_add_seq tl)):
  (i: idx tl {is_blum_add (index tl i) /\
              blum_add_elem (index tl i) = S.index (blum_add_seq tl) j /\
              add_seq_map tl i = j}) =
  add_seq_map_inv_aux tl j              

let rec lemma_add_seq_inv_aux (tl: verifiable_log) (i: idx tl{is_blum_add (index tl i)}):
  Lemma (requires True)
        (ensures (add_seq_inv_map tl (add_seq_map tl i) = i))
        (decreases (length tl)) = 
  let n = length tl in
  assert (n > 0);
  let tl' = prefix tl (n - 1) in
  let s' = blum_add_seq_aux tl' in
  let e = index tl (n - 1) in
  let s = blum_add_seq tl in

  if i = n - 1 then ()
  else
    lemma_add_seq_inv_aux tl' i 

let lemma_add_seq_inv (tl: verifiable_log) (i: idx tl{is_blum_add (index tl i)}):
  Lemma (requires True)
        (ensures (add_seq_inv_map tl (add_seq_map tl i) = i)) =
  lemma_add_seq_inv_aux tl i        

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

let blum_evict_elem = blum_evict_elem_def

let reveal_blum_evict_elem () 
  : Lemma (blum_evict_elem == blum_evict_elem_def)
  = norm_spec [delta_only [`%blum_evict_elem]] blum_evict_elem
  
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
  Lemma (ts_lt (clock_pre tl i) (clock tl i)) = ()

let lemma_evict_timestamp_is_clock (tl: verifiable_log) (i: idx tl{is_evict_to_blum (index tl i)}):
  Lemma (timestamp_of (blum_evict_elem tl i) = clock tl i) = 
  ()

let final_clock (tl:verifiable_log): timestamp =
  Valid?.clk (verify tl)

let lemma_final_clock_monotonic (tl: verifiable_log) (i:idx tl):
  Lemma (ts_leq (final_clock (prefix tl i)) (final_clock tl)) = 
  if i = 0 then ()
  else
    lemma_clock_monotonic tl (i - 1) (length tl - 1)

let rec lemma_evict_clock_leq_final_clock (tl:verifiable_log) (i: SA.seq_index (blum_evict_seq tl)):
  Lemma (requires True)
        (ensures (ts_leq (timestamp_of (S.index (blum_evict_seq tl) i)) (final_clock tl)))
        (decreases (length tl)) = 
  let n = length tl in
  let es = blum_evict_seq tl in
  let be = S.index es i in
  let t = timestamp_of be in
  let c = final_clock tl in
  if n = 0 then ()
  else (
    let tl' = prefix tl (n - 1) in
    let es' = blum_evict_seq tl' in
    let c' = final_clock tl' in
    
    lemma_final_clock_monotonic tl (n - 1);
    assert(ts_leq c' c);
    
    if i < S.length es' then 
      lemma_evict_clock_leq_final_clock tl' i    
    else 
      lemma_evict_timestamp_is_clock tl (n - 1)
  )

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
      //assert(is_evict_to_blum e);
      //assert(timestamp_of (S.index (blum_evict_seq tl) i2) = timestamp_of (blum_evict_elem tl (n - 1)));
             
      lemma_evict_timestamp_is_clock tl (n - 1);
      //assert(timestamp_of (blum_evict_elem tl (n - 1)) =  clock tl (n - 1));
             
      lemma_evict_clock_strictly_increasing tl (n - 1);             
      //assert(ts_lt (clock_pre tl (n - 1)) (clock tl (n - 1)));
      //assert(i1 < S.length es');
      //assert(S.index es i1 = S.index es' i1);
      lemma_evict_clock_leq_final_clock tl' i1;
      ()
    )
  )

let lemma_evict_elem_unique (tl: verifiable_log) (i1 i2: SA.seq_index (blum_evict_seq tl)):
  Lemma (i1 <> i2 ==> S.index (blum_evict_seq tl) i1 <> S.index (blum_evict_seq tl) i2) = 
  if i1 = i2 then ()
  else if i1 < i2 then
    lemma_evict_seq_clock_strictly_monotonic tl i1 i2
  else 
    lemma_evict_seq_clock_strictly_monotonic tl i2 i1

let rec evict_seq_map_aux (tl: verifiable_log) (i: idx tl{is_evict_to_blum (index tl i)}):
  Tot (j: SA.seq_index (blum_evict_seq tl) {S.index (blum_evict_seq tl) j = 
                                        blum_evict_elem tl i})
  (decreases (length tl)) =                                         
  let n = length tl in
  let tl' = prefix tl (n - 1) in
  let s' = blum_evict_seq tl' in  
  if i = n - 1 then
    S.length s'
  else
    evict_seq_map_aux tl' i

let evict_seq_map = evict_seq_map_aux

let rec evict_seq_inv_map_aux (tl: verifiable_log) (j: SA.seq_index (blum_evict_seq tl)):
  Tot(i: idx tl{is_evict_to_blum (index tl i) /\
             blum_evict_elem tl i = S.index (blum_evict_seq tl) j /\
             evict_seq_map tl i = j}) 
  (decreases (length tl)) =             
  let n = length tl in
  let tl' = prefix tl (n - 1) in
  let s' = blum_evict_seq tl' in  
  if j = S.length s' then
    n - 1
  else
    evict_seq_inv_map_aux tl' j

let evict_seq_inv_map = evict_seq_inv_map_aux

let rec lemma_evict_seq_inv_aux (tl: verifiable_log) (i: idx tl{is_evict_to_blum (index tl i)}):
  Lemma (requires True)
        (ensures (evict_seq_inv_map tl (evict_seq_map tl i) = i))
        (decreases (length tl)) = 
  let n = length tl in
  let tl' = prefix tl (n - 1) in
  if i = n - 1 then()
  else lemma_evict_seq_inv_aux tl' i

let lemma_evict_seq_inv = lemma_evict_seq_inv_aux

let lemma_blum_evict_elem_key (tl: verifiable_log) (i: idx tl{is_evict_to_blum (index tl i)}):
  Lemma (MH.key_of (blum_evict_elem tl i) = V.key_of (index tl i)) = 
  ()

let lemma_blum_evict_elem_prefix (tl: verifiable_log) (i: nat{i <= length tl}) 
  (j: nat{j < i && is_evict_to_blum (index tl j)}):
  Lemma (blum_evict_elem tl j = blum_evict_elem (prefix tl i) j) = ()
 
let lemma_add_clock (tl: verifiable_log) (i: idx tl{is_blum_add (index tl i)}):
  Lemma (MH.timestamp_of (blum_add_elem (index tl i)) `ts_lt`  clock tl i) = 
  let e = index tl i in
  lemma_state_transition tl i;
  let si = state_at tl i in
  let si' = state_at tl (i + 1) in
  match e with
  | AddB r t j ->
    assert(Valid?.clk si' = max (Valid?.clk si) (next t)); 
    ()

let lemma_evict_clock (tl: verifiable_log) (i: idx tl{is_evict_to_blum (index tl i)}):
  Lemma (MH.timestamp_of (blum_evict_elem tl i) = clock tl i) = 
  let e = index tl i in  
  lemma_state_transition tl i;
  let si = state_at tl i in
  let si' = state_at tl (i + 1) in
  let be = blum_evict_elem tl i in
  match e with
  | EvictB k t -> 
    //assert(MH.timestamp_of be = t);    
    ()
  | EvictBM k k' t -> ()

