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

#push-options "--z3rlimit_factor 4"
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

let rec blum_add_seq (ep: epoch) (tl: verifiable_log):
  Tot (S.seq ms_hashfn_dom)
  (decreases (length tl)) =
  let n = length tl in
  if n = 0 then S.empty #ms_hashfn_dom
  else
    let tl' = prefix tl (n - 1) in
    let s' = blum_add_seq ep tl' in
    let e = index tl (n - 1) in
    if is_blum_add e && epoch_of (blum_add_elem e) = ep
    then SA.append1 s' (blum_add_elem e)
    else s'

(* map a blum add to an index of the add sequence of the epoch of the add *)
let rec add_seq_map (tl: verifiable_log) (i: idx tl{is_blum_add (index tl i)}):
  Tot (let be = blum_add_elem (index tl i) in
   let ep = epoch_of be in
   let add_seq = blum_add_seq ep tl in
   j: SA.seq_index add_seq{S.index add_seq j = be})
  (decreases (length tl)) =
  let n = length tl in
  let be = blum_add_elem (index tl i) in
  let ep = epoch_of be in
  let tl' = prefix tl (n - 1) in
  let s' = blum_add_seq ep tl' in
  if i = n - 1 then
    S.length s'
  else
    add_seq_map tl' i

let rec add_seq_inv_map (ep: epoch) (tl: verifiable_log) (j: SA.seq_index (blum_add_seq ep tl)):
  Tot (i: idx tl {is_blum_add (index tl i) /\
              blum_add_elem (index tl i) = S.index (blum_add_seq ep tl) j /\
              epoch_of (blum_add_elem (index tl i)) = ep /\
              add_seq_map tl i = j})
  (decreases (length tl)) =
  let n = length tl in
  assert(n > 0);
  let tl' = prefix tl (n - 1) in
  let s' = blum_add_seq ep tl' in
  let e = index tl (n - 1) in
  let s = blum_add_seq ep tl in
  if j = S.length s' then
    n - 1
  else
    add_seq_inv_map ep tl' j

let rec lemma_add_seq_inv (tl: verifiable_log) (i: idx tl{is_blum_add (index tl i)}):
  Lemma (ensures (let be = blum_add_elem (index tl i) in
                  let ep = epoch_of be in
                  add_seq_inv_map ep tl (add_seq_map tl i) = i))
        (decreases (length tl)) =
  let n = length tl in
  assert (n > 0);
  let be = blum_add_elem (index tl i) in
  let ep = epoch_of be in
  let tl' = prefix tl (n - 1) in
  let s' = blum_add_seq ep tl' in
  let e = index tl (n - 1) in

  if i = n - 1 then ()
  else
    lemma_add_seq_inv tl' i

let hadd_at (ep: epoch) (tl: verifiable_log) (i:nat{i <= length tl}): ms_hash_value =
  Valid?.hadd (state_at tl i) ep

let lemma_hadd_unchanged
  (ep: epoch)
  (tl: verifiable_log)
  (i: idx tl{not (is_blum_add (index tl i)) \/ epoch_of (blum_add_elem (index tl i)) <> ep}):
  Lemma (hadd_at ep tl i == hadd_at ep tl (i + 1)) =
  lemma_state_transition tl i;
  ()

let rec lemma_hadd_correct (ep: epoch) (tl: verifiable_log):
  Lemma (ensures (hadd tl ep = ms_hashfn (blum_add_seq ep tl)))
        (decreases (length tl)) =
  let n = length tl in
  if n = 0 then
    lemma_hashfn_empty()
  else (
    let tl' = prefix tl (n - 1) in
    let s' = blum_add_seq ep tl' in
    let e = index tl (n - 1) in
    let h' = hadd tl' in
    lemma_hadd_correct ep tl';
    if is_blum_add e && epoch_of (blum_add_elem e) = ep then lemma_hashfn_app s' (blum_add_elem e)
    else lemma_hadd_unchanged ep tl (n - 1)
  )

let rec blum_evict_seq (ep: epoch) (tl: verifiable_log):
  Tot (S.seq ms_hashfn_dom)
  (decreases (length tl)) = 
  let n = length tl in
  if n = 0 then S.empty #ms_hashfn_dom
  else (
    let tl' = prefix tl (n - 1) in
    let s' = blum_evict_seq ep tl' in
    let e = index tl (n - 1) in
    if is_evict_to_blum e && epoch_of (blum_evict_elem tl (n - 1)) = ep then
      SA.append1 s' (blum_evict_elem tl (n - 1))
    else s'
  )

let hevict_at (ep: epoch) (tl: verifiable_log) (i:nat{i <= length tl}): ms_hash_value =
  Valid?.hevict (state_at tl i) ep

let lemma_hevict_unchanged (ep: epoch) (tl:verifiable_log)
  (i:idx tl{not (is_evict_to_blum (index tl i)) \/ epoch_of (blum_evict_elem tl i) <> ep}):
  Lemma (hevict_at ep tl i = hevict_at ep tl (i + 1)) =
  lemma_state_transition tl i;
  ()

let lemma_hevict_change (ep: epoch) (tl: verifiable_log)
  (i: idx tl{is_evict_to_blum (index tl i) /\ epoch_of (blum_evict_elem tl i) = ep}):
  Lemma (hevict_at ep tl (i + 1) = ms_hashfn_upd (blum_evict_elem tl i) (hevict_at ep tl i)) =
  lemma_state_transition tl i;
  lemma_thread_id_state (prefix tl i);  
  ()

let rec lemma_hevict_correct (ep: epoch) (tl: verifiable_log):
  Lemma (ensures (hevict tl ep = ms_hashfn (blum_evict_seq ep tl)))
        (decreases (length tl)) = 
  let n = length tl in
  if n = 0 then 
    lemma_hashfn_empty()
  else (
    let tl' = prefix tl (n - 1) in
    let s' = blum_evict_seq ep tl' in
    let e = index tl (n - 1) in
    let h' = hevict tl' in
    lemma_hevict_correct ep tl';
    if is_evict_to_blum e && epoch_of (blum_evict_elem tl (n - 1)) = ep then (
      lemma_hashfn_app s' (blum_evict_elem tl (n - 1));
      lemma_hevict_change ep tl (n - 1)
    )
    else 
      lemma_hevict_unchanged ep tl (n - 1)
  )

(* all elements of tl's blum_evict_seq contain tid of tl *)
let rec lemma_evict_elem_tid_aux (ep: epoch) (tl: verifiable_log) (i: SA.seq_index (blum_evict_seq ep tl)):
  Lemma (ensures (MH.thread_id_of (S.index (blum_evict_seq ep tl) i) = (thread_id_of tl)))
        (decreases (length tl))
        [SMTPat (is_of_thread_id (thread_id_of tl) (S.index (blum_evict_seq ep tl) i))] =
  let es = blum_evict_seq ep tl in
  let tid = thread_id_of tl in
  let n = length tl in
  if n = 0 then ()
  else (
    let tl' = prefix tl (n - 1) in
    let es' = blum_evict_seq ep tl' in
    let e = index tl (n - 1) in
    if is_evict_to_blum e && epoch_of (blum_evict_elem tl (n - 1)) = ep then (
      //assert(es == SA.append1 es' (blum_evict_elem tl (n - 1)));
      if i = S.length es - 1 then (
        //assert(S.index es i = (blum_evict_elem tl (n - 1)));        
        ()
      )
      else (
        //assert(S.index es i = S.index es' i);
        lemma_evict_elem_tid_aux ep tl' i
      )
    )
    else lemma_evict_elem_tid_aux ep tl' i
  )

let lemma_evict_elem_tid (ep: epoch) (tl: verifiable_log):
  Lemma (all (is_of_thread_id (thread_id_of tl)) (blum_evict_seq ep tl)) = ()

let clock_pre (tl:verifiable_log) (i:nat { i <= length tl }): timestamp =
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

let rec lemma_evict_clock_leq_final_clock
    (ep: epoch)
    (tl:verifiable_log)
    (i: SA.seq_index (blum_evict_seq ep tl)):
  Lemma (ensures (ts_leq (timestamp_of (S.index (blum_evict_seq ep tl) i)) (final_clock tl)))
        (decreases (length tl)) = 
  let n = length tl in
  let es = blum_evict_seq ep tl in
  let be = S.index es i in
  let t = timestamp_of be in
  let c = final_clock tl in
  if n = 0 then ()
  else (
    let tl' = prefix tl (n - 1) in
    let es' = blum_evict_seq ep tl' in
    let c' = final_clock tl' in
    
    lemma_final_clock_monotonic tl (n - 1);
    assert(ts_leq c' c);
    
    if i < S.length es' then 
      lemma_evict_clock_leq_final_clock ep tl' i
    else 
      lemma_evict_timestamp_is_clock tl (n - 1)
  )

let rec lemma_evict_seq_clock_strictly_monotonic
  (ep: epoch) (tl: verifiable_log) (i1 i2: SA.seq_index (blum_evict_seq ep tl)):
  Lemma (requires (i1 < i2))
        (ensures (ts_lt (timestamp_of (S.index (blum_evict_seq ep tl) i1))
                        (timestamp_of (S.index (blum_evict_seq ep tl) i2))))
        (decreases (length tl)) =
  let n = length tl in
  let es = blum_evict_seq ep tl in
  if n = 0 then ()
  else (
    let tl' = prefix tl (n - 1) in
    let es' = blum_evict_seq ep tl' in
    if i2 < S.length es' then
      lemma_evict_seq_clock_strictly_monotonic ep tl' i1 i2
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
      lemma_evict_clock_leq_final_clock ep tl' i1;
      ()
    )
  )

let lemma_evict_elem_unique (ep: epoch) (tl: verifiable_log) (i1 i2: SA.seq_index (blum_evict_seq ep tl)):
  Lemma (i1 <> i2 ==> S.index (blum_evict_seq ep tl) i1 <> S.index (blum_evict_seq ep tl) i2) =
  if i1 = i2 then ()
  else if i1 < i2 then
    lemma_evict_seq_clock_strictly_monotonic ep tl i1 i2
  else 
    lemma_evict_seq_clock_strictly_monotonic ep tl i2 i1

let rec evict_seq_map (tl: verifiable_log) (i: idx tl{is_evict_to_blum (index tl i)}):
  Tot (let be = blum_evict_elem tl i in
   let ep = epoch_of be in
   let evict_seq = blum_evict_seq ep tl in
   j: SA.seq_index evict_seq {S.index evict_seq j = be})
  (decreases (length tl)) =
  let n = length tl in
  let be = blum_evict_elem tl i in
  let ep = epoch_of be in
  let tl' = prefix tl (n - 1) in
  let s' = blum_evict_seq ep tl' in
  if i = n - 1 then
    S.length s'
  else
    evict_seq_map tl' i

let rec evict_seq_inv_map (ep: epoch) (tl: verifiable_log) (j: SA.seq_index (blum_evict_seq ep tl)):
  Tot (i: idx tl{is_evict_to_blum (index tl i) /\
             blum_evict_elem tl i = S.index (blum_evict_seq ep tl) j /\
             epoch_of (blum_evict_elem tl i) = ep /\
             evict_seq_map tl i = j})
  (decreases (length tl)) =
  let n = length tl in
  let tl' = prefix tl (n - 1) in
  let s' = blum_evict_seq ep tl' in
  if j = S.length s' then
    n - 1
  else
    evict_seq_inv_map ep tl' j

let rec lemma_evict_seq_inv (tl: verifiable_log) (i: idx tl{is_evict_to_blum (index tl i)}):
    Lemma (ensures (let be = blum_evict_elem tl i in
                    let ep = epoch_of be in
                    evict_seq_inv_map ep tl (evict_seq_map tl i) = i))
        (decreases (length tl)) =
  let n = length tl in
  let tl' = prefix tl (n - 1) in
  if i = n - 1 then()
  else lemma_evict_seq_inv tl' i

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

let lemma_addm_ancestor_merkle (tl:verifiable_log) (i:idx tl{is_merkle_add (index tl i)}):
  Lemma (ensures (let AddM _ k' = index tl i in
                  is_merkle_key k')) = 
  let tli = prefix tl i in
  assert(verifiable tli);
  let tli' = prefix tl (i + 1) in
  assert(verifiable tli');
  ()

let lemma_evictm_ancestor_merkle (tl:verifiable_log) (i:idx tl{is_evict_to_merkle (index tl i)}):
  Lemma (ensures (let EvictM _ k' = index tl i in
                  is_merkle_key k')) = 
  let tli = prefix tl i in
  assert(verifiable tli);
  let tli' = prefix tl (i + 1) in
  assert(verifiable tli');
  ()

let lemma_evictbm_ancestor_merkle (tl:verifiable_log) (i:idx tl{EvictBM? (index tl i)}):
  Lemma (ensures (let EvictBM _ k' _ = index tl i in
                  is_merkle_key k')) = 
  let tli = prefix tl i in
  assert(verifiable tli);
  let tli' = prefix tl (i + 1) in
  assert(verifiable tli');
  ()

let epoch_pre (tl: verifiable_log) (i: nat { i <= length tl }) =
  let MkTimestamp e _ = clock_pre tl i in
  e

let epoch_post (tl: verifiable_log) (i: idx tl) =
  let MkTimestamp e _ = clock tl i in
  e

let rec max_epoch_index_search (ep: epoch) (tl: verifiable_log) (i: nat { i <= length tl }):
  Tot (j: nat { j <= i /\ epoch_pre tl j <= ep /\
              (j = i \/ epoch_post tl j > ep)})
  (decreases i) =
  if epoch_pre tl i <= ep then i
  else
    max_epoch_index_search ep tl (i - 1)

let prefix_upto_epoch (ep: epoch) (tl: verifiable_log): verifiable_log =
  let j = max_epoch_index_search ep tl (length tl) in
  prefix tl j

let lemma_prefix_upto_epoch (ep: epoch) (tl: verifiable_log):
  Lemma (ensures (let tl' = prefix_upto_epoch ep tl in
                  let tid, l = tl in
                  let tid', l' = tl' in
                  let MkTimestamp ep' _ = Valid?.clk (verify tl') in
                  tid = tid' /\
                  SA.is_prefix l l' /\
                  ep' <= ep /\
                  (length tl' < length tl ==> (let MkTimestamp ep'' _ = clock tl (length tl') in
                                               ep'' > ep)))) = ()
