module Veritas.Verifier.CorrectDefs

open FStar.Seq
open Veritas.BinTree
open Veritas.EAC
open Veritas.Interleave
open Veritas.MultiSetHash
open Veritas.Record
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

let requires_key_in_cache (e:vlog_entry): bool = 
  match e with
  | Get _ _ -> true
  | Put _ _ -> true
  | EvictM _ _ -> true
  | EvictB _ _ -> true
  | EvictBM _ _ _ -> true
  | _ -> false

let lemma_requires_key_in_cache (st: vtls) (e:vlog_entry{requires_key_in_cache e && 
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
    let itsl' = its_prefix itsl (m - 1) in
    let r' = time_seq_ext itsl' in
    let (id,e) = telem itsl in
    
    admit()
  )

let lemma_its_prefix_ext (#n:nat) (itsl:its_log n) (i:nat{i <= length itsl}):
  Lemma (requires True)
        (ensures (time_seq_ext (its_prefix itsl i) = prefix (time_seq_ext itsl) i))
        [SMTPat (time_seq_ext (its_prefix itsl i))] = 
  admit()
