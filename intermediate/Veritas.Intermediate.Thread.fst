module Veritas.Intermediate.Thread

let lemma_init_store_ismap (vcfg:verifier_config) (tid:thread_id)
  : Lemma (ensures (is_map (init_store vcfg tid))) =
  let st = empty_store vcfg in
  lemma_empty_store_is_map #vcfg;
  lemma_empty_contains_nokey #vcfg Root;
  if tid = 0 then
    lemma_madd_root_to_store_is_map st 0 (init_value Root)
  else ()

let lemma_init_store_slot_points_to_is_merkle_points_to (vcfg:verifier_config) (tid:thread_id)
  : Lemma (ensures (slot_points_to_is_merkle_points_to (init_store vcfg tid))) =
  let st = init_store vcfg tid in
  let aux (s1 s2: slot_id vcfg) (d: bin_tree_dir):
    Lemma (ensures (not (points_to_dir st s1 d s2)))
          [SMTPat (slot_points_to_is_merkle_points_to_local st s1 s2 d)] =
    if tid = 0 then
      ()
    else ()
  in
  ()

let rec verifiable_implies_prefix_verifiable_aux
  (#vcfg:_) (tl:verifiable_log vcfg) (i:nat{i <= length tl}):
  Lemma (ensures (verifiable (prefix tl i)))
        (decreases (length tl)) =
  let n = length tl in
  if i = n then ()
  else
    verifiable_implies_prefix_verifiable_aux (prefix tl (n - 1)) i

let verifiable_implies_prefix_verifiable = verifiable_implies_prefix_verifiable_aux

#push-options "--z3rlimit_factor 8"
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

let rec blum_add_seq (#vcfg:_) (ep: epoch) (tl: verifiable_log vcfg):
  Tot (S.seq ms_hashfn_dom)
  (decreases (length tl)) =
  let n = length tl in
  if n = 0 then S.empty #ms_hashfn_dom
  else
    let tl' = prefix tl (n - 1) in
    let s' = blum_add_seq ep tl' in
    let e = index tl (n - 1) in
    if is_blum_add e && epoch_of (blum_add_elem e) = ep  then SA.append1 s' (blum_add_elem e)
    else s'

let rec add_seq_map (#vcfg:_) (tl: verifiable_log vcfg) (i: seq_index tl{is_blum_add (index tl i)}):
  Tot (let be = blum_add_elem (index tl i) in
   let ep = epoch_of be in
   let add_seq = blum_add_seq ep tl in
   j: SA.seq_index add_seq {S.index add_seq j = be})
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

let rec add_seq_inv_map (#vcfg:_) (ep: epoch) (tl: verifiable_log vcfg) (j: SA.seq_index (blum_add_seq ep tl)):
  Tot (i: seq_index tl {is_blum_add (index tl i) /\
                    blum_add_elem (index tl i) = S.index (blum_add_seq ep tl) j /\
                    epoch_of (blum_add_elem (index tl i)) = ep /\
                    add_seq_map tl i = j})
  (decreases (length tl)) =
  let n = length tl in
  assert(n > 0);
  let tl' = prefix tl (n - 1) in
  let s' = blum_add_seq ep tl' in
  let e = index tl (n - 1) in
  if j = S.length s' then
    n - 1
  else
    add_seq_inv_map ep tl' j

let rec lemma_add_seq_inv (#vcfg:_) (tl: verifiable_log vcfg) (i: seq_index tl{is_blum_add (index tl i)}):
  Lemma (ensures (let be = blum_add_elem (index tl i) in
                  let ep = epoch_of be in
                  add_seq_inv_map ep tl (add_seq_map tl i) = i))
        (decreases (length tl)) =
  let n = length tl in
  assert (n > 0);
  let tl' = prefix tl (n - 1) in

  if i = n - 1 then ()
  else
    lemma_add_seq_inv tl' i

let lemma_state_transition #vcfg (tl: verifiable_log vcfg) (i: seq_index tl):
  Lemma (state_at tl (i + 1) ==
         verify_step (state_at tl i) (index tl i)) =
  ()

let hadd_at #vcfg (ep: epoch) (tl: verifiable_log vcfg) (i:nat{i <= length tl}): ms_hash_value =
  Valid?.hadd (state_at tl i) ep

let lemma_hadd_unchanged
  #vcfg
  (ep: epoch)
  (tl: verifiable_log vcfg)
  (i: seq_index tl{ not (is_blum_add (index tl i)) \/ epoch_of (blum_add_elem (index tl i)) <> ep}):
  Lemma (hadd_at ep tl i == hadd_at ep tl (i + 1)) =
  lemma_state_transition tl i;
  ()

let rec lemma_hadd_correct #vcfg (ep: epoch) (tl: verifiable_log vcfg):
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

let rec blum_evict_seq #vcfg (ep: epoch) (tl: verifiable_log vcfg):
  Tot (S.seq ms_hashfn_dom)
  (decreases (length tl)) =
  let n = length tl in
  if n = 0 then S.empty #ms_hashfn_dom
  else (
    let tl' = prefix tl (n - 1) in
    let s' = blum_evict_seq ep tl' in
    let e = index tl (n - 1) in
    if is_evict_to_blum e && epoch_of (blum_evict_elem tl (n-1)) = ep then
      SA.append1 s' (blum_evict_elem tl (n - 1))
    else s'
  )

let hevict_at #vcfg (ep: epoch) (tl: verifiable_log vcfg) (i:nat{i <= length tl}): ms_hash_value =
  Valid?.hevict (state_at tl i) ep

let lemma_hevict_unchanged #vcfg
  (ep: epoch)
  (tl:verifiable_log vcfg)
  (i:seq_index tl{not (is_evict_to_blum (index tl i)) \/ epoch_of (blum_evict_elem tl i) <> ep}):
  Lemma (hevict_at ep tl i = hevict_at ep tl (i + 1)) =
  lemma_state_transition tl i;
  ()

let rec lemma_thread_id_state #vcfg (tl: verifiable_log vcfg):
  Lemma (ensures (IntV.thread_id_of (verify tl) = thread_id_of tl))
        (decreases (length tl)) =
  let n = length tl in
  if n = 0 then ()
  else
    lemma_thread_id_state (prefix tl (n - 1))

module Spec = Veritas.Verifier

let lemma_hevict_change #vcfg (ep: epoch) (tl: verifiable_log vcfg)
  (i: seq_index tl{is_evict_to_blum (index tl i) /\ epoch_of (blum_evict_elem tl i) = ep}):
  Lemma (hevict_at ep tl (i + 1) = ms_hashfn_upd (blum_evict_elem tl i) (hevict_at ep tl i)) =
  lemma_state_transition tl i;
  lemma_thread_id_state (prefix tl i)

let rec lemma_hevict_correct #vcfg (ep: epoch) (tl: verifiable_log vcfg):
  Lemma (ensures (hevict tl ep = ms_hashfn (blum_evict_seq ep tl)))
        (decreases (length tl)) =
  let n = length tl in
  if n = 0 then
    lemma_hashfn_empty()
  else (
    let tl' = prefix tl (n - 1) in
    let s' = blum_evict_seq ep tl' in
    let e = index tl (n - 1) in
    lemma_hevict_correct ep tl';
    if is_evict_to_blum e && epoch_of (blum_evict_elem tl (n-1)) = ep then (
      lemma_hashfn_app s' (blum_evict_elem tl (n - 1));
      lemma_hevict_change ep tl (n - 1)
    )
    else
      lemma_hevict_unchanged ep tl (n - 1)
  )

let rec evict_seq_map
  (#vcfg:_)
  (tl: verifiable_log vcfg)
  (i: seq_index tl{is_evict_to_blum (index tl i)}):
  Tot (let be = blum_evict_elem tl i in
   let ep = epoch_of be in
   let evict_seq = blum_evict_seq ep tl in
   j: SA.seq_index (blum_evict_seq ep tl) {S.index evict_seq j = be})
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

let rec evict_seq_inv_map (#vcfg:_) (ep: epoch) (tl: verifiable_log vcfg) (j: SA.seq_index (blum_evict_seq ep tl)):
  Tot(i: seq_index tl{is_evict_to_blum (index tl i) /\
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

let rec lemma_evict_seq_inv
  (#vcfg:_)
  (tl: verifiable_log vcfg)
  (i: seq_index tl{is_evict_to_blum (index tl i)}):
  Lemma (ensures (let be = blum_evict_elem tl i in
                  let ep = epoch_of be in
                  evict_seq_inv_map ep tl (evict_seq_map tl i) = i))
        (decreases (length tl)) =
  let n = length tl in
  let be = blum_evict_elem tl i in
  let ep = epoch_of be in
  let tl' = prefix tl (n - 1) in
  if i = n - 1 then ()
  else
    lemma_evict_seq_inv tl' i

let lemma_blum_evict_elem_prefix (#vcfg:_) (tl: verifiable_log vcfg) (i: nat{i <= length tl})
  (j: nat{j < i && is_evict_to_blum (index tl j)}):
  Lemma (blum_evict_elem tl j = blum_evict_elem (prefix tl i) j) = ()

#push-options "--max_fuel 1 --max_ifuel 0"

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

#pop-options

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

let rec lemma_evict_elem_tid_aux #vcfg
  (ep: epoch)
  (tl:verifiable_log vcfg)
  (i: SA.seq_index (blum_evict_seq ep tl)):
  Lemma (ensures (MH.thread_id_of (S.index (blum_evict_seq ep tl) i) = (thread_id_of tl)))
        (decreases (length tl))
        [SMTPat (is_of_thread_id (thread_id_of tl) (S.index (blum_evict_seq ep tl) i))] =
  let es = blum_evict_seq ep tl in
  let tid = thread_id_of tl in
  let n = length tl in
  if n = 0 then ()
  else
    let tl' = prefix tl (n - 1) in
    let es' = blum_evict_seq ep tl' in
    let e = index tl (n - 1) in
    if is_evict_to_blum e && epoch_of (blum_evict_elem tl (n-1)) = ep then
      if i = S.length es - 1 then
        ()
      else
        lemma_evict_elem_tid_aux ep tl' i
    else
      lemma_evict_elem_tid_aux ep tl' i

let lemma_evict_elem_tid (#vcfg:_) (ep: epoch) (tl:verifiable_log vcfg):
  Lemma (all (is_of_thread_id (thread_id_of tl)) (blum_evict_seq ep tl)) = ()

let clock_pre #vcfg (tl:verifiable_log vcfg) (i:nat {i <= length tl}): timestamp =
  Valid?.clock (state_at tl i)

let lemma_evict_clock_strictly_increasing #vcfg (tl: verifiable_log vcfg) (i: seq_index tl {is_evict_to_blum (index tl i)}):
  Lemma (ts_lt (clock_pre tl i) (clock tl i)) = ()

let lemma_evict_timestamp_is_clock #vcfg (tl: verifiable_log vcfg) (i: seq_index tl{is_evict_to_blum (index tl i)}):
  Lemma (timestamp_of (blum_evict_elem tl i) = clock tl i) =
  ()

let final_clock #vcfg (tl:verifiable_log vcfg): timestamp =
  Valid?.clock (verify tl)

#push-options "--max_fuel 1 --max_ifuel 0"
let lemma_clock_monotonic #vcfg (tl: verifiable_log vcfg) (i:seq_index tl) (j:seq_index tl{j >= i}):
  Lemma (clock tl i `ts_leq` clock tl j) =
  let tlj = prefix tl (j + 1) in
  lemma_clock_monotonic_aux tlj i
#pop-options

let lemma_final_clock_monotonic #vcfg (tl: verifiable_log vcfg) (i:seq_index tl):
  Lemma (ts_leq (final_clock (prefix tl i)) (final_clock tl)) =
  if i = 0 then ()
  else
    lemma_clock_monotonic tl (i - 1) (length tl - 1)

let rec lemma_evict_clock_leq_final_clock #vcfg (ep: epoch)
  (tl:verifiable_log vcfg) (i: SA.seq_index (blum_evict_seq ep tl)):
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

let rec lemma_evict_seq_clock_strictly_monotonic #vcfg
  (ep: epoch) (tl: verifiable_log vcfg) (i1 i2: SA.seq_index (blum_evict_seq ep tl)):
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

let lemma_evict_elem_unique (#vcfg:_) (ep: epoch)
  (tl: verifiable_log vcfg) (i1 i2: SA.seq_index (blum_evict_seq ep tl)):
  Lemma (i1 <> i2 ==> S.index (blum_evict_seq ep tl) i1 <> S.index (blum_evict_seq ep tl) i2) =
  if i1 = i2 then ()
  else if i1 < i2 then
    lemma_evict_seq_clock_strictly_monotonic ep tl i1 i2
  else
    lemma_evict_seq_clock_strictly_monotonic ep tl i2 i1

let epoch_pre #vcfg (tl: verifiable_log vcfg) (i: nat { i <= length tl }) =
  let MkTimestamp e _ = clock_pre tl i in
  e

let epoch_post #vcfg (tl: verifiable_log vcfg) (i: seq_index tl) =
  let MkTimestamp e _ = clock tl i in
  e

let rec max_epoch_index_search #vcfg (ep: epoch)
  (tl: verifiable_log vcfg) (i: nat { i <= length tl }):
  Tot (j: nat { j <= i /\ epoch_pre tl j <= ep /\
              (j = i \/ epoch_post tl j > ep)})
  (decreases i) =
  if epoch_pre tl i <= ep then i
  else
    max_epoch_index_search ep tl (i - 1)

(* Get the maximal prefix of log upto epoch "ep" *)
let prefix_upto_epoch (#vcfg:_) (ep: epoch) (tl: verifiable_log vcfg): verifiable_log vcfg =
  let j = max_epoch_index_search ep tl (length tl) in
  prefix tl j

let lemma_prefix_upto_epoch (#vcfg:_) (ep: epoch) (tl: verifiable_log vcfg):
  Lemma (ensures (let tl' = prefix_upto_epoch ep tl in
                  let tid, l = tl in
                  let tid', l' = tl' in
                  let MkTimestamp ep' _ = Valid?.clock (verify tl') in
                  tid = tid' /\
                  SA.is_prefix l l' /\
                  ep' <= ep /\
                  (length tl' < length tl ==> (let MkTimestamp ep'' _ = clock tl (length tl') in
                                               ep'' > ep)))) = ()
