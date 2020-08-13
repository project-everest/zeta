module Veritas.Verifier.Correctness

open FStar.Seq
open Veritas.EAC
open Veritas.Hash
open Veritas.Interleave
open Veritas.Key
open Veritas.MultiSetHash
open Veritas.Record
open Veritas.SeqAux
open Veritas.SeqMachine
open Veritas.StateSeqMachine
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

(* state ops of all vlogs of all verifier threads *)
let to_state_op_gvlog (gl: g_vlog) =
  map to_state_op_vlog gl

(* generalized single- and multi-set hash collision *)
type hash_collision_gen =
  | SingleHashCollision: hc: hash_collision -> hash_collision_gen
  | MultiHashCollision: hc: ms_hash_collision -> hash_collision_gen


let time_seq_ext (gl: g_verifiable_log):
  (le:vlog_ext{to_vlog le = time_seq gl})
  = admit()

let eac_glog = gl: g_hash_verifiable_log { eac (time_seq_ext gl) }
let non_eac_glog = gl : g_hash_verifiable_log { ~ (eac (time_seq_ext gl)) }

let lemma_time_seq_not_eac_implies_hash_collision (gl:non_eac_glog): hash_collision_gen = 
  let tmsle = time_seq_ext gl in

  (* the key causing the eac violation *)
  let k:key = invalidating_key eac_sm tmsle in

  (* the sequence of log ops of key k *)
  let tmsle_k = partn eac_sm k tmsle in

  (* index i in tmsle_k causes the violation *)
  let i = max_valid_prefix eac_smk tmsle_k in
  assert(iskey vlog_entry_key k (index tmsle_k i));

  (* the maximal valid eac_prefix of tmsle_k *)
  let tmsle_ki = prefix tmsle_k i in
  let tmsle_ki1 = prefix tmsle_k (i + 1) in
  let e:vlog_entry_ext = index tmsle_k i in  
  assert(valid eac_smk tmsle_ki);
  assert(not (valid eac_smk tmsle_ki1));
  assert(vlog_entry_key e = k);

  //assert(vlog_entry_key e = kc);
  let st = seq_machine_run eac_smk tmsle_ki in

  match st with
  | EACInit -> 
    (
      match e with
      | NEvict (Get k' v') -> 
        assert(k' = k);
        admit()
      | _ -> admit()
    )
  | EACInCache m v -> admit()
  | EACEvicted m v -> admit()

let lemma_time_seq_rw_consistent
  (gl: g_hash_verifiable_log { ~ (rw_consistent (to_state_op_vlog (time_seq gl)))}): hash_collision_gen =

  (* time sequence log *)
  let tmsle = time_seq_ext gl in
  let tmsl = time_seq gl in

  (* sequence of state ops in time sequence *)
  let tm_ops = to_state_op_vlog tmsl in
  assert(~ (rw_consistent tm_ops));

  (* is time seq log evict add consistent? *)
  let is_eac = valid_all_comp eac_sm tmsle in

  (* if tmsle is evict add consistent then tm_ops is rw_consistent, a contradiction *)
  if is_eac then (
     lemma_eac_implies_rw_consistent tmsle;
     assert(rw_consistent tm_ops);

     (* any return value *)
     SingleHashCollision (Collision (DVal Null) (DVal Null))
  )
  else
    lemma_time_seq_not_eac_implies_hash_collision gl

let lemma_vlog_interleave_implies_state_ops_interleave (l: vlog) (gl: g_vlog{interleave l gl}):
  Lemma (interleave (to_state_op_vlog l) (to_state_op_gvlog gl)) = admit()

(* final verifier correctness theorem *)
let lemma_verifier_correct (gl: g_hash_verifiable_log { ~ (seq_consistent (to_state_op_gvlog gl))}):
  hash_collision_gen =

  (* sequences of per-thread put/get operations *)
  let g_ops = to_state_op_gvlog gl in

  (* sequence ordered by time of each log entry *)
  let tmsl = time_seq gl in
  assert(interleave tmsl gl);

  (* sequence of state ops induced by tmsl *)
  let tm_ops = to_state_op_vlog tmsl in

  lemma_vlog_interleave_implies_state_ops_interleave tmsl gl;
  assert(interleave tm_ops g_ops);

  (* if tm_ops is read-write consistent then we have a contradiction *)
  let is_rw_consistent = valid_all_comp ssm tm_ops in

  if is_rw_consistent then (

    assert(valid_all ssm tm_ops);
    lemma_state_sm_equiv_rw_consistent tm_ops;
    assert(rw_consistent tm_ops);

    (* a contradiction *)
    assert(seq_consistent g_ops);

    (* any return value *)
    SingleHashCollision (Collision (DVal Null) (DVal Null))
  )
  else
    (* otherwise we can produce a collision *)
    lemma_time_seq_rw_consistent gl
