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

(* globally verifiable logs *)
type g_verifiable (lg:g_vlog) =   
  forall (i:nat{i < length lg}). {:pattern t_verifiable (i, (index lg i))}
  t_verifiable (i, (index lg i))

(* Refinement type of logs that are verifiable *)
type g_verifiable_log = l:g_vlog{g_verifiable l}

(* aggregate hadd over all verifier threads *)
let rec g_hadd (lg:g_verifiable_log) (e:nat)
  : Tot ms_hash_value (decreases (length lg)) = 
  let n = length lg in
  if n = 0 then empty_hash_value
  else 
    let lg' = prefix lg (n - 1) in
    let hv' = g_hadd lg' e in
    let l = index lg (n - 1) in
    // TODO: how to remove this side-effect assert?
    assert(t_verifiable ((n - 1), l));
    let h = thread_hadd (t_verify (n-1) l) e in
    ms_hashfn_agg hv' h  

(* aggregate hadd over all verifier threads *)
let rec g_hevict (lg:g_verifiable_log) (e:nat)
  : Tot ms_hash_value (decreases (length lg)) = 
  let n = length lg in
  if n = 0 then empty_hash_value
  else 
    let lg' = prefix lg (n - 1) in
    let hv' = g_hevict lg' e in
    let l = index lg (n - 1) in
    // TODO: how to remove this side-effect assert?
    assert(t_verifiable  ((n - 1), l));
    let h = thread_hevict (t_verify (n- 1) l) e in
    ms_hashfn_agg hv' h  

(* 
 * a global log is hash verifiable if add and 
 * evict hashes agree for every epoch 
 *)
let g_hash_verifiable (lg: g_verifiable_log) = 
  forall (e:nat). g_hadd lg e = g_hevict lg e

(* refinement type of hash verifiable log *)
let g_hash_verifiable_log = 
  lg:g_verifiable_log {g_hash_verifiable lg}

(* the clock of a verifier thread after processing a verifiable log *)
let clock_after (il:t_verifiable_log) = 
  let vs = t_verify (tid il) (vlog_of il) in
  Valid?.clk vs

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

type clocked_vlog_entry = vlog_entry * timestamp

type clocked_vlog = seq (clocked_vlog_entry)

(* construct an augmented vlog with the clock
 * attached to every vlog entry *)
let rec attach_clock (tl:t_verifiable_log): 
  Tot (clocked_vlog) 
  (decreases (tv_length tl)) = 
  let n = tv_length tl in
  if n = 0 then empty 
  else 
    let tl' = tv_prefix tl (n - 1) in
    let cl' = attach_clock tl' in
    let t = clock_after tl in
    let e = tv_index tl (n - 1) in
    append1 cl' (e, t)


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
