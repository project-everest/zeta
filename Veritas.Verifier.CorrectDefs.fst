module Veritas.Verifier.CorrectDefs

open FStar.Seq
open Veritas.BinTree
open Veritas.EAC
open Veritas.Interleave
open Veritas.Key
open Veritas.MultiSetHash
open Veritas.Record
open Veritas.SeqMachine
open Veritas.SeqAux
open Veritas.Verifier

(*
 * an indexed vlog attaches an nat index to a vlog
 * indicating the id of the verifier thread processing
 * the log
 *)
type tid_vlog = nat * vlog

(* thread id of the indexed vlog *)
let tid (il: tid_vlog): nat = fst il

(* vlog of an indexed vlog *)
let vlog_of (il: tid_vlog): vlog = snd il

(* length of the vlog portion *)
let tv_length (tl: tid_vlog): nat =
  length (vlog_of tl)

(* element at the i'th position of the vlog *)
let tv_index (tl: tid_vlog) (i:nat{i < tv_length tl}): vlog_entry =
  index (vlog_of tl) i

(* append an element at the end of the vlog *)
let tv_append1 (tl: tid_vlog) (e: vlog_entry): tid_vlog =
  (tid tl), (append1 (vlog_of tl) e)

(* prefix of a tid_vlog: apply prefix on the
 * vlog component *)
let tv_prefix (tl: tid_vlog) (i:nat{i <= tv_length tl}): tid_vlog =
  (tid tl), (prefix (vlog_of tl) i)

(* does the log leave the verifier thread in a valid state *)
let t_verifiable (il: tid_vlog): bool =
  Valid? (t_verify (tid il) (vlog_of il))

(* refinement types of valid verifier logs *)
type t_verifiable_log = il: tid_vlog {t_verifiable il}

(* Full collection of verifier logs one per thread *)
type g_vlog = seq vlog

(* a slightly different view of verifier log obtained by
 * attaching a tid (index) to each thread verifier log *)
let g_tid_vlog (gl: g_vlog) = attach_index gl

(* globally verifiable logs: every thread-level log is verifiable *)
type g_verifiable (gl:g_vlog) = all t_verifiable (g_tid_vlog gl)

(* Refinement type of logs that are verifiable *)
type g_verifiable_log = l:g_vlog{g_verifiable l}

(* view gl as a sequence of t_verifiable_logs *)
let g_verifiable_refine (gl: g_verifiable_log): seq t_verifiable_log
  = seq_refine t_verifiable (g_tid_vlog gl)

(* aggregate hadd over all verifier threads *)
let g_hadd (gl: g_verifiable_log): ms_hash_value =
  let th = fun (tl:t_verifiable_log) -> (thread_hadd (t_verify (fst tl) (snd tl))) in
  let f = fun (tl:t_verifiable_log) (h:ms_hash_value) -> (ms_hashfn_agg (th tl) h) in
  reduce empty_hash_value f (g_verifiable_refine gl)

(* aggregate hadd over all verifier threads *)
let g_hevict (gl: g_verifiable_log): ms_hash_value =
  let th = fun (tl:t_verifiable_log) -> (thread_hevict (t_verify (fst tl) (snd tl))) in
  let f = fun (tl:t_verifiable_log) (h:ms_hash_value) -> (ms_hashfn_agg (th tl) h) in
  reduce empty_hash_value f (g_verifiable_refine gl)

(*
 * a global log is hash verifiable if add and
 * evict hashes agree
 *)
let g_hash_verifiable (lg: g_verifiable_log): bool =
  g_hadd lg = g_hevict lg

(* refinement type of hash verifiable log *)
type g_hash_verifiable_log =
  lg:g_verifiable_log {g_hash_verifiable lg}

let rec lemma_verifiable_implies_prefix_verifiable
  (tl:t_verifiable_log) (i:nat{i <= tv_length tl}):
  Lemma (requires (True))
        (ensures (t_verifiable (tv_prefix tl i)))
        (decreases (tv_length tl))
        [SMTPat (tv_prefix tl i)]
        =
  let n = tv_length tl in
  if n = 0 then ()
  else if i = n then ()
  else
    lemma_verifiable_implies_prefix_verifiable (tv_prefix tl (n - 1)) i

(* the clock of a verifier thread after processing a verifiable log *)
let clock_after (tl:t_verifiable_log): timestamp =
  let vs = t_verify (tid tl) (vlog_of tl) in
  Valid?.clk vs

(* the clock of a verifier is monotonic *)
let rec lemma_clock_monotonic (tl:t_verifiable_log) (i:nat{i <= tv_length tl}):
  Lemma (requires(True))
        (ensures (clock_after (tv_prefix tl i) `ts_leq` clock_after tl))
  (decreases (tv_length tl))
        =
  let n = tv_length tl in
  if n = 0 then ()
  else if i = n then ()
  else
    let tl' = tv_prefix tl (n - 1) in
    lemma_clock_monotonic tl' i

(* We assign a time to every entry thread log *)
let t_entry_time (tl: t_verifiable_log) (i:nat{i < tv_length tl}): timestamp =
  let tl' = tv_prefix tl (i+1) in
  clock_after tl'

(* the clock of entry j <= clock of entry i if j occurs before i *)
let lemma_time_monotonic_in_thread (tl: t_verifiable_log) (i:nat{i < tv_length tl}) (j:nat{j <= i}):
  Lemma (requires (True))
        (ensures (t_entry_time tl j `ts_leq` t_entry_time tl i)) =
  let tli = tv_prefix tl (i + 1) in
  lemma_clock_monotonic tli (j + 1)

(* Time of an entry in global verifiable log *)
let g_entry_time (gl: g_verifiable_log) (si: sseq_index gl): timestamp =
  let (i,j) = si in
  let tl = index (g_tid_vlog gl) i in
  t_entry_time tl j

(* define time sequence obtained by ordering all log entries across all threads
 * by their assigned time as defined above *)
let time_seq_ctor (gl: g_verifiable_log):
  Tot (interleave_ctor gl) =
  admit()

let time_seq (gl: g_verifiable_log)
  = interleaved_seq gl (time_seq_ctor gl)

(* map every entry of the time sequence to its source entry in the thread logs *)
let time_seq_source (gl: g_verifiable_log) (i: seq_index (time_seq gl)): sseq_index gl =
  interleave_map (time_seq gl) gl (interleaving_prf gl (time_seq_ctor gl)) i

(* if i <= j are two indexes in the time_seq, then the time of entry i <= time of entry j*)
let lemma_time_seq_correct (gl: g_verifiable_log)
                           (i: seq_index (time_seq gl))
                           (j: seq_index (time_seq gl){j >= i}):
  Lemma (g_entry_time gl (time_seq_source gl i) `ts_leq` g_entry_time gl (time_seq_source gl j))
  = admit()

let requires_key_in_store (e:vlog_entry): bool = 
  match e with
  | Get _ _ -> true
  | Put _ _ -> true
  | EvictM _ _ -> true
  | EvictB _ _ -> true
  | EvictBM _ _ _ -> true
  | _ -> false

let lemma_requires_key_in_store (st: vtls) (e:vlog_entry{requires_key_in_store e && 
                                                         Valid? (t_verify_step st e)}):
  Lemma (Valid? st && store_contains (thread_store st) (vlog_entry_key e)) = 
  ()

let lemma_root_never_evicted (st:vtls) (e:vlog_entry{is_evict e && 
                                        Valid? (t_verify_step st e)}):
  Lemma (vlog_entry_key e <> Root) = ()

let evict_value (il:t_verifiable_log) (i:nat{i < tv_length il /\
                                            is_evict (tv_index il i)}): value =
  let (id, l) = il in
  let li = prefix l i in
  lemma_verifiable_implies_prefix_verifiable il i;
  let vsi = t_verify id li in
  let sti = thread_store vsi in
  let li' = prefix l (i + 1) in
  
  lemma_verifiable_implies_prefix_verifiable il (i + 1);
  let vsi' = t_verify id li' in
  assert(Valid? vsi');
  let e = index l i in
  assert(vsi' == t_verify_step vsi e);
  match e with
  | EvictM k _ -> 
    stored_value sti k 
  | EvictB k _ -> stored_value sti k
  | EvictBM k _ _ -> stored_value sti k

type its_log (n:nat) = 
  s:seq (idx_elem #vlog_entry n){g_verifiable (partition_idx_seq s)}

(* the prefix of an its log *)
let its_prefix (#n:nat) (itsl: its_log n) (i:nat{i <= length itsl}): 
  (itsl':its_log n{length itsl' = i}) =
  let itsl': seq (idx_elem #vlog_entry n) = prefix itsl i in
  let gl = partition_idx_seq itsl in
  let idgl = g_tid_vlog gl in
  
  let gl' = partition_idx_seq itsl' in
  let idgl' = g_tid_vlog gl' in

  let aux (id:nat{id < n}):
    Lemma (requires True)
          (ensures (t_verifiable (index idgl' id)))
          [SMTPat (t_verifiable (index idgl' id))]    
    = 
    let (_,l') = index idgl' id in
    //let (_,l) = index idgl id in    
    lemma_partition_idx_prefix_comm itsl i  id;
    lemma_verifiable_implies_prefix_verifiable (index idgl id) (length l');
    ()
  in
  itsl'


(* extended time sequence log (with evict values) *)
let rec time_seq_ext (#n:nat) (itsl: its_log n):
  Tot (le:vlog_ext{project_seq itsl = to_vlog le})
  (decreases (length itsl))
  =
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
    let r' = time_seq_ext itsl' in

    (* project seq of itsl and itsl' differ by log entry e *)
    lemma_unzip_extend itsl;
    assert(project_seq itsl = append1 (project_seq itsl') e);

    if is_evict e then (
      (* log entries of verifier thread id *)
      let gl = partition_idx_seq itsl in
      let l = index gl id in
      assert(snd (index (g_tid_vlog gl) id) = l);

      (* since l is verifiable, the value at last position is well-defined *)
      assert(t_verifiable (id, l));
      (* prove length l > 0 *)
      lemma_partition_idx_extend1 itsl;

      let v = evict_value (id, l) (length l - 1) in

      let r = append1 r' (Evict e v) in
      lemma_prefix1_append r' (Evict e v);
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

let lemma_its_prefix_ext (#n:nat) (itsl:its_log n) (i:nat{i <= length itsl}):
  Lemma (requires True)
        (ensures (time_seq_ext (its_prefix itsl i) = prefix (time_seq_ext itsl) i))
        [SMTPat (time_seq_ext (its_prefix itsl i))] = 
  admit()

type eac_ts_log (n:nat) = itsl: its_log n {is_eac_log (time_seq_ext itsl)}
type non_eac_ts_log (n:nat) = itsl: its_log n {not (is_eac_log (time_seq_ext itsl))}

(* the eac state of a key after processing an eac_log *)
let eac_state_key (le: vlog_ext) (k:key): eac_state = 
  let lek = partn eac_sm k le in
  seq_machine_run eac_smk lek

(* the eac state of a key at the end of an its log *)
let eac_state_of_key (#n:nat) (itsl: its_log n) (k:key): eac_state = 
  let tsle = time_seq_ext itsl in 
  let tslek = partn eac_sm k tsle in
  seq_machine_run eac_smk tslek

(* is the eac state of key at the end of its_log init *)
let is_eac_state_init (#n:nat) (itsl: its_log n) (k:key): bool =
  eac_state_of_key itsl k = EACInit

(* is the key k in evicted state in *)
let is_eac_state_evicted (#n:nat) (itsl: its_log n) (k:key): bool = 
  EACEvicted? (eac_state_of_key itsl k)

(* is the key k in instore state after processing its_log *)
let is_eac_state_instore (#n:nat) (itsl: its_log n) (k:key):bool = 
  EACInStore? (eac_state_of_key itsl k)

(* the state of a verifier thread after processing entries in a log *)
let verifier_thread_state (#n:nat) (itsl: its_log n) (id:nat{id < n}): (st:vtls{Valid? st}) = 
  let gl = partition_idx_seq itsl in
  assert(t_verifiable (index (attach_index gl) id));
  t_verify id (index gl id)

(* 
 * when the eac state of a key is Init (no operations on the key yet) no 
 * thread contains the key in its store 
 *)
let lemma_eac_state_init_store 
   (#n:nat) 
   (itsl: eac_ts_log n) (k: key{k <> Root && is_eac_state_init itsl k}) (id:nat{id < n}):
   Lemma (not (store_contains (thread_store (verifier_thread_state itsl id)) k)) 
   = admit()

(* when the eac state of a key is EACEvicted then no thread contains the key in its store *)
let lemma_eac_state_evicted_store (#n:nat) (itsl: eac_ts_log n) 
  (k: key{is_eac_state_evicted itsl k}) (id:nat{id < n}):
    Lemma (not (store_contains (thread_store (verifier_thread_state itsl id)) k)) = admit()

(* does a log have some add entry *)
let has_some_add (l:seq vlog_entry): bool = 
  exists_sat_elems is_add l

(* does a log have some add of key k *)
let has_some_add_of_key (k:key) (l:seq vlog_entry): bool = 
  exists_sat_elems (is_add_of_key k) l 
  
(* when the eac state of a key is "instore" then there is always a previous add *)
let lemma_eac_state_instore_implies_prev_add (#n:nat) (itsl: eac_ts_log n) (k:key{is_eac_state_instore itsl k}):
  Lemma (has_some_add_of_key k (project_seq itsl)) = admit()

(* when the eac state of a key is instore return the index of the last add that transitioned
 * the key k to "instore" *)
let last_add_idx (#n:nat) (itsl: eac_ts_log n) (k: key{is_eac_state_instore itsl k}): seq_index itsl =
   lemma_eac_state_instore_implies_prev_add itsl k;
   last_index (is_add_of_key k) (project_seq itsl)

(* the verifier thread where the last add of key k happens *)
let last_add_tid (#n:nat) (itsl: eac_ts_log n) (k: key{is_eac_state_instore itsl k}): (tid:nat{tid < n}) =
  snd (index itsl (last_add_idx itsl k))

(* if the eac_state of k is instore, then that k is in the store of the verifier thread of its last add *)
let lemma_eac_state_instore (#n:nat) (itsl: eac_ts_log n) (k:key{is_eac_state_instore itsl k}):
  Lemma (store_contains (thread_store (verifier_thread_state itsl (last_add_tid itsl k))) k) = admit()

(* if the eac state of k is instore, then k is not in the store of any verifier thread other than 
 * its last add thread *)
let lemma_eac_state_instore2 (#n:nat) (itsl: eac_ts_log n) (k:key{is_eac_state_instore itsl k}) (id:nat{id < n}):
  Lemma (requires (id <> last_add_tid itsl k))
        (ensures (not (store_contains (thread_store (verifier_thread_state itsl id)) k))) = admit()

(* the root is always in thread 0 *)
let lemma_root_in_store0 (#n:pos) (itsl: eac_ts_log n):
  Lemma (store_contains (thread_store (verifier_thread_state itsl 0)) Root) = admit()

let lemma_root_not_in_store (#n:pos) (itsl: eac_ts_log n) (tid:pos {tid < n}):
  Lemma (not (store_contains (thread_store (verifier_thread_state itsl tid)) Root)) = admit()

(* the evicted value is always of the correct type for the associated key *)
let lemma_evict_value_correct_type (#n:pos) (itsl: eac_ts_log n) (k:key{is_eac_state_evicted itsl k}):
  Lemma (is_value_of k (EACEvicted?.v (eac_state_of_key itsl k))) = admit()

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
    | EACEvicted _ v -> lemma_evict_value_correct_type itsl k; v
    | EACInStore _ _ -> 
      (* the store where the last add happened contains key k *)
      let tid = last_add_tid itsl k in
      let st = thread_store (verifier_thread_state itsl tid) in
        
      lemma_eac_state_instore itsl k;
      assert(store_contains st k);

      stored_value st k
