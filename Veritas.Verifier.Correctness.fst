module Veritas.Verifier.Correctness

open FStar.Seq
open Veritas.Hash
open Veritas.Interleave
open Veritas.Key
open Veritas.MultiSetHash
open Veritas.Record
open Veritas.SeqAux
open Veritas.State
open Veritas.Verifier

//Allow the solver to unroll recursive functions at most once (fuel)
//Allow the solver to invert inductive definitions at most once (ifuel)
#push-options "--max_fuel 1 --max_ifuel 1 --initial_fuel 1 --initial_ifuel 1"

(* 
 * an indexed vlog attaches an nat index to a vlog 
 * indicating the id of the verifier thread processing
 * the log 
 *)
type tid_vlog = nat * vlog

(* thread id of the indexed vlog *)
let tid (il: tid_vlog) = fst il

(* vlog of an indexed vlog *)
let vlog_of (il: tid_vlog) = snd il

(* length of the vlog portion *)
let tv_length (tl: tid_vlog) = 
  length (vlog_of tl)

(* element at the i'th position of the vlog *)
let tv_index (tl: tid_vlog) (i:nat{i < tv_length tl}) = 
  index (vlog_of tl) i

(* append an element at the end of the vlog *)
let tv_append1 (tl: tid_vlog) (e: vlog_entry): Tot tid_vlog = 
  (tid tl), (append1 (vlog_of tl) e)

(* prefix of a tid_vlog: apply prefix on the 
 * vlog component *)
let tv_prefix (tl: tid_vlog) (i:nat{i <= tv_length tl}): Tot tid_vlog = 
  (tid tl), (prefix (vlog_of tl) i)

(* does the log leave the verifier thread in a valid state *)
let t_verifiable (il: tid_vlog) = 
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
let g_verifiable_refine (gl: g_verifiable_log): Tot (seq t_verifiable_log)
  = seq_refine t_verifiable (g_tid_vlog gl)

(* aggregate hadd over all verifier threads *)
let g_hadd (gl: g_verifiable_log) (e:nat) = 
  let he = fun (tl:t_verifiable_log) -> (thread_hadd (t_verify (fst tl) (snd tl)) e) in
  let f = fun (tl:t_verifiable_log) (h:ms_hash_value) -> (ms_hashfn_agg (he tl) h) in     
  reduce empty_hash_value f (g_verifiable_refine gl)

(* aggregate hadd over all verifier threads *)
let g_hevict (gl: g_verifiable_log) (e:nat) = 
  let ha = fun (tl:t_verifiable_log) -> (thread_hevict (t_verify (fst tl) (snd tl)) e) in
  let f = fun (tl:t_verifiable_log) (h:ms_hash_value) -> (ms_hashfn_agg (ha tl) h) in     
  reduce empty_hash_value f (g_verifiable_refine gl)  

(* 
 * a global log is hash verifiable if add and 
 * evict hashes agree for every epoch 
 *)
let g_hash_verifiable (lg: g_verifiable_log) = 
  forall (e:nat). g_hadd lg e = g_hevict lg e

(* refinement type of hash verifiable log *)
let g_hash_verifiable_log = 
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
let clock_after (tl:t_verifiable_log) = 
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
let t_entry_time (tl: t_verifiable_log) (i:nat{i < tv_length tl}) =   
  let tl' = tv_prefix tl (i+1) in  
  clock_after tl'

(* the clock of entry j <= clock of entry i if j occurs before i *)
let lemma_time_monotonic_in_thread (tl: t_verifiable_log) (i:nat{i < tv_length tl}) (j:nat{j <= i}):
  Lemma (requires (True))
        (ensures (t_entry_time tl j `ts_leq` t_entry_time tl i)) = 
  let tli = tv_prefix tl (i + 1) in
  lemma_clock_monotonic tli (j + 1)

(* Time of an entry in global verifiable log *)
let g_entry_time (gl: g_verifiable_log) (i: sseq_index gl) = admit()

(* define time sequence obtained by ordering all log entries across all threads 
 * by their assigned time as defined above *)
let time_seq_ctor (gl: g_verifiable_log): 
  Tot (interleave_ctor gl) =
  admit()

let time_seq (gl: g_verifiable_log) = interleaved_seq gl (time_seq_ctor gl)

(* map every entry of the time sequence to its origin entry in the thread logs *)
let time_seq_source (gl: g_verifiable_log) (i: seq_index (time_seq gl)) =
  interleave_map (time_seq gl) gl (interleaving_prf gl (time_seq_ctor gl)) i


(* the state operations of a vlog *)
let is_state_op (e: vlog_entry) = 
  match e with
  | Get k v -> true
  | Put k v -> true 
  | _ -> false

(* map vlog entry to state op *)
let to_state_op (e:vlog_entry {is_state_op e}) = 
  match e with
  | Get k v -> Veritas.State.Get k v
  | Put k v -> Veritas.State.Put k v

(* filter out the state ops of vlog *)
let to_state_op_vlog (l: vlog) = 
  map to_state_op (filter_refine is_state_op l)

(* state ops of all vlogs of all verifier threads *)
let to_state_op_gvlog (gl: g_vlog) = 
  map to_state_op_vlog gl

(* generalized single- and multi-set hash collision *)
type hash_collision_gen = 
  | SingleHashCollision: hc: hash_collision -> hash_collision_gen 
  | MultiHashCollision: hc: ms_hash_collision -> hash_collision_gen

(* final verifier correctness theorem *)
let lemma_verifier_correct (lg: g_hash_verifiable_log { ~ (seq_consistent (to_state_op_gvlog lg))}):
  Tot hash_collision_gen = admit()
