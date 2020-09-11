module Veritas.Verifier.TSLog

let clock_sorted (il: il_vlog{verifiable il}) =
 forall (i j:I.seq_index il). i <= j ==> clock il i `ts_leq` clock il j

module SA = Veritas.SeqAux
open FStar.Calc

let lemma_prefix_clock_sorted (itsl: its_log) (i:nat{i <= I.length itsl})
  : Lemma
    (requires
      verifiable (I.prefix itsl i))
    (ensures
      clock_sorted (I.prefix itsl i))
  = assert (clock_sorted itsl);
    let itsl' = I.prefix itsl i in
    let aux (t0 t1:I.seq_index itsl')
      : Lemma (requires t0 <= t1)
              (ensures clock itsl' t0 `ts_leq` clock itsl' t1)
              [SMTPat(clock itsl' t0 `ts_leq` clock itsl' t1)]
      = assert (clock itsl t0 `ts_leq` clock itsl t1);
        lemma_i2s_map_prefix itsl i t0;
        lemma_i2s_map_prefix itsl i t1;
        I.lemma_prefix_index itsl i t0;
        I.lemma_prefix_index itsl i t1;
        I.per_thread_prefix itsl i;
        //This "calc" feature lets you structure
        //proofs by equational rewriting ... each line is
        //equal to the next line and the whole calc term
        //proves that the first line is equal to the last
        //
        calc (==) {
         clock itsl' t0;
          == {}
         clock (I.prefix itsl i) t0;
          == {}
         VG.clock (g_vlog_of itsl') (i2s_map itsl' t0);
          == {}
         VG.clock (g_vlog_of itsl') (i2s_map itsl t0);
        }
    in
    ()

let lemma_prefix_verifiable (itsl: its_log) (i:nat{i <= I.length itsl})
  : Lemma
    (ensures
      verifiable (I.prefix itsl i) /\
      clock_sorted (I.prefix itsl i))
  = assert (verifiable itsl);
    assert (clock_sorted itsl);
    let ss = g_vlog_of itsl in
    let itsl' = I.prefix itsl i in
    let ss' = g_vlog_of itsl' in
    assert (Seq.length ss = Seq.length ss');
    let aux (tid:SA.seq_index ss)
      : Lemma (VT.verifiable (thread_log ss' tid))
              [SMTPat (thread_log ss' tid)]
      = let tl = thread_log ss tid in
        assert (VT.verifiable tl);
        I.per_thread_prefix itsl i;
        let tl' = thread_log ss' tid in
        let aux (j:SA.seq_index (snd tl))
          : Lemma
            (requires snd tl' == SA.prefix (snd tl) j)
            (ensures VT.verifiable tl')
            [SMTPat (SA.prefix (snd tl) j)]
          = assert (tl' == VT.prefix tl j);
            VT.lemma_verifiable_implies_prefix_verifiable tl j
        in
        ()
    in
    lemma_prefix_clock_sorted itsl i

let create (gl: VG.verifiable_log)
  =  admit()

let lemma_create_correct (gl: VG.verifiable_log):
  Lemma (gl = to_g_vlog (create gl)) = admit()

let thread_state (#p:pos) (itsl: its_log p) (tid: valid_tid p): (vs:vtls{Valid? vs}) = 
  let gl = partition_idx_seq itsl in
  let tl = VG.thread_log gl tid in
  VT.verify tl

let lemma_verifier_thread_state_extend (#p:pos) (itsl: its_log p) (i:seq_index itsl):
  Lemma (thread_state (prefix itsl (i + 1)) (thread_id_of itsl i)== 
         t_verify_step (thread_state (prefix itsl i) (thread_id_of itsl i))
                       (vlog_entry_at itsl i)) = 
  let gl = partition_idx_seq itsl in                       
  let tid = thread_id_of itsl i in                       
  
  admit()                       

(* extended time sequence log (with evict values) 
let rec time_seq_ext_aux (#p:pos) (itsl: its_log p):
  Tot (le:vlog_ext{project_seq itsl = to_vlog le})
  (decreases (length itsl)) =*)
  (*
  let m = length itsl in
  if m = 0 then (
    lemma_empty itsl;
    lemma_empty (project_seq itsl);
    let r = empty #vlog_entry_ext in
    lemma_empty (to_vlog r);
    r
  )
  else (
    let (e,id) = telem itsl in

    (* recurse *)
    let itsl' = its_prefix itsl (m - 1) in
    let r' = time_seq_ext_aux itsl' in

    (* project seq of itsl and itsl' differ by log entry e *)
    lemma_project_seq_extend itsl;
    assert(project_seq itsl = append1 (project_seq itsl') e);

    (* log entries of verifier thread id *)
    let gl = partition_idx_seq itsl in
    let l = index gl id in
    assert(snd (index (g_tid_vlog gl) id) = l);

    (* since l is verifiable, the value at last position is well-defined *)
    assert(VT.verifiable (id, l));
    (* prove length l > 0 *)
    lemma_partition_idx_extend1 itsl;

    if is_evict_to_merkle e then (
      let v = evict_value (id, l) (length l - 1) in
      let r = append1 r' (EvictMerkle e v) in
      lemma_prefix1_append r' (EvictMerkle e v);
      lemma_map_extend to_vlog_entry r;
      r
    )
    else if is_evict_to_blum e then (
      let v = evict_value (id, l) (length l - 1) in
      let r = append1 r' (EvictBlum e v id) in
      lemma_prefix1_append r' (EvictBlum e v id);
      lemma_map_extend to_vlog_entry r;
      r
    )
    else (
      let r = append1 r' (NEvict e) in
      lemma_prefix1_append r' (NEvict e);
      lemma_map_extend to_vlog_entry r;
      r
    )
  )
  *)


let rec lemma_its_prefix_ext (#n:pos) (itsl:its_log n) (i:nat{i <= length itsl}):
  Lemma (requires True)
        (ensures (time_seq_ext (its_prefix itsl i) = prefix (time_seq_ext itsl) i)) 
        (decreases (length itsl)) = 
  let n = length itsl in          
  if i = n then ()
  else (
    assert(n > 0 && i < n);

    if i = n - 1 then
      admit()
    else

    admit()
  )

(* if itsl is eac, then any prefix is also eac *)
let lemma_eac_implies_prefix_eac (#p:pos) (itsl: eac_ts_log p) (i:nat {i <= length itsl}):
  Lemma (requires True)
        (ensures (is_eac_log (its_prefix itsl i)))
        [SMTPat (its_prefix itsl i)] = admit()

(* 
 * when the eac state of a key is Init (no operations on the key yet) no 
 * thread contains the key in its store 
 *)
let lemma_eac_state_init_store 
   (#p:pos) 
   (itsl: eac_ts_log p) (k: key{k <> Root && is_eac_state_init itsl k}) (id:nat{id < p}):
   Lemma (not (store_contains (thread_store (verifier_thread_state itsl id)) k)) 
   = admit()

(* when the eac state of a key is EACEvicted then no thread contains the key in its store *)
let lemma_eac_state_evicted_store (#p:pos) (itsl: eac_ts_log p) 
  (k: key{is_eac_state_evicted itsl k}) (id:nat{id < p}):
    Lemma (not (store_contains (thread_store (verifier_thread_state itsl id)) k)) = admit()

(* when the eac state of a key is "instore" then there is always a previous add *)
let lemma_eac_state_instore_implies_prev_add (#p:pos) (itsl: eac_ts_log p) (k:key{is_eac_state_instore itsl k}):
  Lemma (has_some_add_of_key k (project_seq itsl)) = admit()

(* if the eac_state of k is instore, then that k is in the store of the verifier thread of its last add *)
let lemma_eac_state_instore (#p:pos) (itsl: eac_ts_log p) (k:key{is_eac_state_instore itsl k}):
  Lemma (store_contains (thread_store (verifier_thread_state itsl (last_add_tid itsl k))) k /\
         stored_value (thread_store (verifier_thread_state itsl (last_add_tid itsl k))) k = 
         EACInStore?.v (eac_state_of_key itsl k)) = admit()

let lemma_eac_state_instore_addm (#p:pos) (itsl: eac_ts_log p) (k:key{is_eac_state_instore itsl k}):
  Lemma (is_add (index (project_seq itsl) (last_add_idx itsl k)) /\
         store_contains (thread_store (verifier_thread_state itsl (last_add_tid itsl k))) k /\
         EACInStore?.m (eac_state_of_key itsl k) = 
         addm_of_entry (index (project_seq itsl) (last_add_idx itsl k)) /\
         EACInStore?.m (eac_state_of_key itsl k) = 
         add_method_of (thread_store (verifier_thread_state itsl (last_add_tid itsl k))) k) = admit()

(* if the eac state of k is instore, then k is not in the store of any verifier thread other than 
 * its last add thread *)
let lemma_eac_state_instore2 (#p:pos) (itsl: eac_ts_log p) 
  (k:key{is_eac_state_instore itsl k}) (id:nat{id < p}):
  Lemma (requires (id <> last_add_tid itsl k))
        (ensures (not (store_contains (thread_store (verifier_thread_state itsl id)) k))) = admit()

let lemma_instore_implies_eac_state_instore (#p:pos) (itsl:eac_ts_log p) (k:key{k <> Root}) (tid:nat{tid < p}):
  Lemma (store_contains (thread_store (verifier_thread_state itsl tid)) k ==> is_eac_state_instore itsl k) = 
  admit()

(* the root is always in thread 0 *)
let lemma_root_in_store0 (#p:pos) (itsl: eac_ts_log p):
  Lemma (store_contains (thread_store (verifier_thread_state itsl 0)) Root) = admit()

let lemma_root_not_in_store (#p:pos) (itsl: eac_ts_log p) (tid:pos {tid < p}):
  Lemma (not (store_contains (thread_store (verifier_thread_state itsl tid)) Root)) = admit()

(* the evicted value is always of the correct type for the associated key *)
let lemma_evict_value_correct_type (#p:pos) (itsl: eac_ts_log p) (k:key{is_eac_state_evicted itsl k}):
  Lemma (is_value_of k (E.value_of (eac_state_of_key itsl k))) = admit()

(* 
 * for keys in a thread store, return the value in the thread store; 
 * for other keys return the last evict value or null (init)
 *)
let eac_value (#n:pos) (itsl: eac_ts_log n) (k:key): value_type_of k = 
  if k = Root then (
    lemma_root_in_store0 itsl;
    stored_value (thread_store (verifier_thread_state itsl 0)) Root
  )
  else 
    let es = eac_state_of_key itsl k in
    match es with
    | EACInit -> init_value k 
    | EACEvictedMerkle v -> lemma_evict_value_correct_type itsl k; v
    | EACEvictedBlum v _ _ -> lemma_evict_value_correct_type itsl k; v
    | EACInStore _ _ -> 
      (* the store where the last add happened contains key k *)
      let tid = last_add_tid itsl k in
      let st = thread_store (verifier_thread_state itsl tid) in
        
      lemma_eac_state_instore itsl k;
      assert(store_contains st k);

      stored_value st k

let lemma_eac_value_is_stored_value (#p:pos) (itsl: eac_ts_log p) (k:key) (id:nat{id < p}):
  Lemma (requires (store_contains (thread_store (verifier_thread_state itsl id)) k))
        (ensures (eac_value itsl k = 
                  stored_value (thread_store (verifier_thread_state itsl id)) k)) = admit()

let lemma_eac_value_is_evicted_value (#p:pos) (itsl: eac_ts_log p) (k:key):
  Lemma (requires (is_eac_state_evicted itsl k))
        (ensures (eac_state_evicted_value itsl k = eac_value itsl k)) = admit()

let lemma_ext_evict_val_is_stored_val (#p:pos) (itsl: its_log p) (i: seq_index itsl):
  Lemma (requires (is_evict (fst (index itsl i))))
        (ensures (is_evict_ext (index (time_seq_ext itsl) i) /\
                  store_contains (thread_store (verifier_thread_state (its_prefix itsl i)
                                                                      (snd (index itsl i))))
                                 (V.key_of (fst (index itsl i))) /\
                  value_ext (index (time_seq_ext itsl) i) = 
                  stored_value (thread_store (verifier_thread_state (its_prefix itsl i)
                                                                    (snd (index itsl i))))
                               (V.key_of (fst (index itsl i))))) = admit()


let lemma_evict_has_next_add (#p:pos) (itsl: its_log p) (i:seq_index itsl):
  Lemma (requires (is_evict (index itsl i) /\
                   exists_sat_elems (entry_of_key (key_of (index itsl i))) itsl) /\
                   i < last_idx_of_key itsl (key_of (index itsl i)))
        (ensures (has_next_add_of_key itsl i (key_of (index itsl i)))) = admit()
