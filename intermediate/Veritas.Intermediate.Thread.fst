module Veritas.Intermediate.Thread

let lemma_init_store_ismap (vcfg:verifier_config) (tid:thread_id)
  : Lemma (ensures (is_map (init_store vcfg tid))) = admit()

let lemma_init_store_slot_points_to_is_merkle_points_to (vcfg:verifier_config) (tid:thread_id)
  : Lemma (ensures (slot_points_to_is_merkle_points_to (init_store vcfg tid))) = admit()

let rec verifiable_implies_prefix_verifiable_aux
  (#vcfg:_) (tl:verifiable_log vcfg) (i:nat{i <= length tl}):
  Lemma (ensures (verifiable (prefix tl i)))
        (decreases (length tl)) = 
  let n = length tl in
  if i = n then ()
  else
    verifiable_implies_prefix_verifiable_aux (prefix tl (n - 1)) i

let verifiable_implies_prefix_verifiable = verifiable_implies_prefix_verifiable_aux

let rec blum_add_seq_aux (#vcfg:_) (tl: verifiable_log vcfg): 
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

let blum_add_seq (#vcfg:_) (tl: verifiable_log vcfg): S.seq ms_hashfn_dom = 
  blum_add_seq_aux tl

let rec add_seq_map_aux (#vcfg:_) (tl: verifiable_log vcfg) (i: seq_index tl{is_blum_add (index tl i)}):
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

let add_seq_map (#vcfg:_) (tl: verifiable_log vcfg) (i: seq_index tl{is_blum_add (index tl i)}):
  (j: SA.seq_index (blum_add_seq tl){S.index (blum_add_seq tl) j =
                                     blum_add_elem (index tl i)}) = add_seq_map_aux tl i

let rec add_seq_inv_map_aux (#vcfg:_) (tl: verifiable_log vcfg) (j: SA.seq_index (blum_add_seq tl)):
  Tot (i: seq_index tl {is_blum_add (index tl i) /\
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
      add_seq_inv_map_aux tl' j

let add_seq_inv_map (#vcfg:_) (tl: verifiable_log vcfg) (j: SA.seq_index (blum_add_seq tl)):
  (i: seq_index tl {is_blum_add (index tl i) /\
              blum_add_elem (index tl i) = S.index (blum_add_seq tl) j /\
              add_seq_map tl i = j}) = add_seq_inv_map_aux tl j

let rec lemma_add_seq_inv_aux (#vcfg:_) (tl: verifiable_log vcfg) (i: seq_index tl{is_blum_add (index tl i)}):
  Lemma (ensures (add_seq_inv_map tl (add_seq_map tl i) = i))
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

let lemma_add_seq_inv (#vcfg:_) (tl: verifiable_log vcfg) (i: seq_index tl{is_blum_add (index tl i)}):
  Lemma (ensures (add_seq_inv_map tl (add_seq_map tl i) = i)) = lemma_add_seq_inv_aux tl i

(* the verifier state after processing i entries *)
let state_at #vcfg (tl: verifiable_log vcfg) (i:nat{i <= length tl}): st:vtls _{Valid? st} =
  (verify (prefix tl i))

let hadd_at #vcfg (tl: verifiable_log vcfg) (i:nat{i <= length tl}): ms_hash_value =
  Valid?.hadd (state_at tl i)

let lemma_state_transition #vcfg (tl: verifiable_log vcfg) (i: seq_index tl):
  Lemma (state_at tl (i + 1) ==
         verify_step (state_at tl i) (index tl i)) = 
  ()

let lemma_hadd_unchanged #vcfg (tl: verifiable_log _) (i: seq_index tl{not (is_blum_add (index tl i))}):
  Lemma (hadd_at tl i == hadd_at tl (i + 1)) = 
  lemma_state_transition #vcfg tl i;
  ()

let rec lemma_hadd_correct_aux #vcfg (tl: verifiable_log vcfg):
  Lemma (ensures (hadd tl = ms_hashfn (blum_add_seq tl)))
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

let lemma_hadd_correct (#vcfg:_) (tl: verifiable_log vcfg):
  Lemma (ensures (hadd tl = ms_hashfn (blum_add_seq tl))) = lemma_hadd_correct_aux tl

let rec blum_evict_seq_aux #vcfg (tl: verifiable_log vcfg): 
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

let blum_evict_seq (#vcfg:_) (tl: verifiable_log vcfg): S.seq ms_hashfn_dom = blum_evict_seq_aux tl

let hevict_at #vcfg (tl: verifiable_log vcfg) (i:nat{i <= length tl}): ms_hash_value =
  Valid?.hevict (state_at tl i)

let lemma_hevict_unchanged #vcfg (tl:verifiable_log vcfg) (i:seq_index tl{not (is_evict_to_blum (index tl i))}):
  Lemma (hevict_at tl i = hevict_at tl (i + 1)) = ()

let rec lemma_thread_id_state #vcfg (tl: verifiable_log vcfg):
  Lemma (ensures (IntV.thread_id_of (verify tl) = thread_id_of tl))
        (decreases (length tl)) =
  let n = length tl in
  if n = 0 then ()
  else
    lemma_thread_id_state (prefix tl (n - 1))

module Spec = Veritas.Verifier

let lemma_hevict_change #vcfg (tl: verifiable_log vcfg) (i: seq_index tl{is_evict_to_blum (index tl i)}):
  Lemma (hevict_at tl (i + 1) = ms_hashfn_upd (blum_evict_elem tl i) (hevict_at tl i)) = 
  lemma_state_transition tl i;  
  lemma_thread_id_state (prefix tl i)

let rec lemma_hevict_correct_aux #vcfg (tl: verifiable_log vcfg):
  Lemma (ensures (hevict tl = ms_hashfn (blum_evict_seq tl)))
        (decreases (length tl)) = 
  let n = length tl in
  if n = 0 then 
    lemma_hashfn_empty()
  else (
    let tl' = prefix tl (n - 1) in
    let s' = blum_evict_seq tl' in
    let s = blum_evict_seq tl in
    let e = index tl (n - 1) in
    let h' = hevict tl' in
    let h = hevict tl in
    lemma_hevict_correct_aux tl';  
    if is_evict_to_blum e then (    
      lemma_hashfn_app s' (blum_evict_elem tl (n - 1));
      lemma_hevict_change tl (n - 1)
    )
    else
      lemma_hevict_unchanged tl (n - 1)   
  )

let lemma_hevict_correct (#vcfg:_) (tl: verifiable_log vcfg):
  Lemma (hevict tl = ms_hashfn (blum_evict_seq tl)) = lemma_hevict_correct_aux tl

let rec evict_seq_map_aux (#vcfg:_) (tl: verifiable_log vcfg) (i: seq_index tl{is_evict_to_blum (index tl i)}):
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

let evict_seq_map (#vcfg:_) (tl: verifiable_log vcfg) (i: seq_index tl{is_evict_to_blum (index tl i)}):
  (j: SA.seq_index (blum_evict_seq tl) {S.index (blum_evict_seq tl) j = 
                                        blum_evict_elem tl i}) = evict_seq_map_aux tl i

let rec evict_seq_inv_map_aux (#vcfg:_) (tl: verifiable_log vcfg) (j: SA.seq_index (blum_evict_seq tl)):
  Tot (i: seq_index tl{is_evict_to_blum (index tl i) /\
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

let evict_seq_inv_map (#vcfg:_) (tl: verifiable_log vcfg) (j: SA.seq_index (blum_evict_seq tl)):
  (i: seq_index tl{is_evict_to_blum (index tl i) /\
             blum_evict_elem tl i = S.index (blum_evict_seq tl) j /\
             evict_seq_map tl i = j}) = evict_seq_inv_map_aux tl j

let rec lemma_evict_seq_inv_aux (#vcfg:_) (tl: verifiable_log vcfg) (i: seq_index tl{is_evict_to_blum (index tl i)}):
  Lemma (ensures (evict_seq_inv_map tl (evict_seq_map tl i) = i))
        (decreases (length tl)) =
  let n = length tl in
  let tl' = prefix tl (n - 1) in
  if i = n - 1 then ()
  else
    lemma_evict_seq_inv_aux tl' i

let lemma_evict_seq_inv (#vcfg:_) (tl: verifiable_log vcfg) (i: seq_index tl{is_evict_to_blum (index tl i)}):
  Lemma (ensures (evict_seq_inv_map tl (evict_seq_map tl i) = i)) = lemma_evict_seq_inv_aux tl i

let lemma_blum_evict_elem_prefix (#vcfg:_) (tl: verifiable_log vcfg) (i: nat{i <= length tl}) 
  (j: nat{j < i && is_evict_to_blum (index tl j)}):
  Lemma (blum_evict_elem tl j = blum_evict_elem (prefix tl i) j) = ()

let lemma_add_clock (#vcfg:_) (tl: verifiable_log vcfg) (i: seq_index tl{is_blum_add (index tl i)}):
  Lemma (timestamp_of (blum_add_elem (index tl i)) `ts_lt`  clock tl i) = 
  let e = index tl i in
  lemma_state_transition tl i;
  let si = state_at tl i in
  let si' = state_at tl (i + 1) in
  match e with
  | AddB_S s r t j ->
    assert(Valid?.clock si' = Spec.max (Valid?.clock si) (next t));
    ()

let lemma_evict_clock (#vcfg:_) (tl: verifiable_log vcfg) (i: seq_index tl{is_evict_to_blum (index tl i)}):
  Lemma (timestamp_of (blum_evict_elem tl i) = clock tl i)  = 
  let e = index tl i in
  lemma_state_transition tl i;
  let si = state_at tl i in
  let si' = state_at tl (i + 1) in
  match e with
  | EvictB_S s t ->
    ()
  | EvictBM_S s s' t -> ()

module MH = Veritas.MultiSetHash

let rec lemma_evict_elem_tid_aux #vcfg (tl:verifiable_log vcfg) (i: SA.seq_index (blum_evict_seq tl)):
  Lemma (ensures (MH.thread_id_of (S.index (blum_evict_seq tl) i) = (thread_id_of tl))) 
        (decreases (length tl))
        [SMTPat (is_of_thread_id (thread_id_of tl) (S.index (blum_evict_seq tl) i))] = 
  let es = blum_evict_seq tl in
  let tid = thread_id_of tl in
  let n = length tl in
  if n = 0 then ()
  else
    let tl' = prefix tl (n - 1) in
    let es' = blum_evict_seq tl' in
    let e = index tl (n - 1) in
    if is_evict_to_blum e then
      if i = S.length es - 1 then
        ()
      else
        lemma_evict_elem_tid_aux tl' i    
    else
      lemma_evict_elem_tid_aux tl' i    
  
let lemma_evict_elem_tid (#vcfg:_) (tl:verifiable_log vcfg):
  Lemma (all (is_of_thread_id (thread_id_of tl)) (blum_evict_seq tl)) = ()

let clock_pre #vcfg (tl:verifiable_log vcfg) (i:seq_index tl): timestamp = 
  Valid?.clock (state_at tl i)

let lemma_evict_clock_strictly_increasing #vcfg (tl: verifiable_log vcfg) (i: seq_index tl {is_evict_to_blum (index tl i)}):
  Lemma (ts_lt (clock_pre tl i) (clock tl i)) = ()

let lemma_evict_timestamp_is_clock #vcfg (tl: verifiable_log vcfg) (i: seq_index tl{is_evict_to_blum (index tl i)}):
  Lemma (timestamp_of (blum_evict_elem tl i) = clock tl i) = 
  ()

let final_clock #vcfg (tl:verifiable_log vcfg): timestamp =
  Valid?.clock (verify tl)

#push-options "--z3rlimit_factor 4"
(* the clock of a verifier is monotonic *)
let rec lemma_clock_monotonic_aux #vcfg (tl:verifiable_log vcfg) (i:seq_index tl):
  Lemma (ensures (clock tl i `ts_leq` clock tl (length tl - 1)))
  (decreases (length tl))
        =
  let n = length tl in
  if n = 0 then ()
  else if i = n - 1 then ()
  else
    let tl' = prefix tl (n - 1) in
    lemma_clock_monotonic_aux tl' i
#pop-options

let lemma_clock_monotonic #vcfg (tl: verifiable_log vcfg) (i:seq_index tl) (j:seq_index tl{j >= i}):
  Lemma (clock tl i `ts_leq` clock tl j) =
  let tlj = prefix tl (j + 1) in
  lemma_clock_monotonic_aux tlj i

let lemma_final_clock_monotonic #vcfg (tl: verifiable_log vcfg) (i:seq_index tl):
  Lemma (ts_leq (final_clock (prefix tl i)) (final_clock tl)) = 
  if i = 0 then ()
  else
    lemma_clock_monotonic tl (i - 1) (length tl - 1)

let rec lemma_evict_clock_leq_final_clock #vcfg (tl:verifiable_log vcfg) (i: SA.seq_index (blum_evict_seq tl)):
  Lemma (ensures (ts_leq (timestamp_of (S.index (blum_evict_seq tl) i)) (final_clock tl)))
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

let rec lemma_evict_seq_clock_strictly_monotonic #vcfg (tl: verifiable_log vcfg) (i1 i2: SA.seq_index (blum_evict_seq tl)):
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

let lemma_evict_elem_unique (#vcfg:_) (tl: verifiable_log vcfg) (i1 i2: SA.seq_index (blum_evict_seq tl)):
  Lemma (i1 <> i2 ==> S.index (blum_evict_seq tl) i1 <> S.index (blum_evict_seq tl) i2) = 
  if i1 = i2 then ()
  else if i1 < i2 then
    lemma_evict_seq_clock_strictly_monotonic tl i1 i2
  else 
    lemma_evict_seq_clock_strictly_monotonic tl i2 i1
 
