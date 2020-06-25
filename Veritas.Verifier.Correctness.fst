module Veritas.Verifier.Correctness

open FStar.Seq
open Veritas.Hash
open Veritas.Key
open Veritas.MultiSetHash
open Veritas.Record
open Veritas.SeqAux
open Veritas.SeqOps
open Veritas.State
open Veritas.Verifier

//Allow the solver to unroll recursive functions at most once (fuel)
//Allow the solver to invert inductive definitions at most once (ifuel)
#push-options "--max_fuel 1 --max_ifuel 1 --initial_fuel 1 --initial_ifuel 1"

(* Does the verifier return Valid (success) for this log *)
let verifiable (#p:pos) (l:vlog) = Valid? (verifier #p l)

(* Refinement type of logs that are verifiable *)
type verifiable_log (#p:pos) = l:vlog{verifiable #p l}

(* If a log is verifiable, then each prefix of the log is also verifiable *)
let rec lemma_verifiable_implies_prefix_verifiable (#p:pos) (l:verifiable_log #p) (i:nat{i <= length l}):
  Lemma (requires (True))
        (ensures (verifiable #p (prefix l i)))
        (decreases (length l)) 
        [SMTPat (prefix l i)]
        =
  let n = length l in
  if n = 0 then ()
  else if i = n then ()
  else
    lemma_verifiable_implies_prefix_verifiable #p (prefix l (n - 1)) i

(* 
 * each verifier thread is independent of all other threads except for the 
 * global multiset hashes: it reads and writes local state and only writes (but does not 
 * read) global state. This means if we take a vlog l, partition it and run each thread 
 * log separately, we should get the same sequence of thread states. We prove this formally.
 *)

(* thread id of a vlog entry *)
let thread_id (#p:pos) (e: vlog_entry_g #p) = TOp?.tid e

(* thread if of an vlog identified by an index *)
let thread_id_idx (#p:pos) (l:vlog) (i:vl_index l) = thread_id #p (index l i)

(* partition the verification log by thread id *)
let vlog_by_thread (#p:pos) (l:vlog): ss: (seq vlog){length ss = p} = 
  partition #(vlog_entry_g #p) #p l (thread_id #p)

(* get the vlog projected to a verifier thread i *)
let vlog_of_thread (#p:pos) (l:vlog) (i:nat{i < p}): vlog = 
  index (vlog_by_thread #p l) i

let lemma_thread_local (#p:pos) (l:verifiable_log) (i:nat{i < p}):
  Lemma (requires (True))
        (ensures (verifiable (vlog_of_thread #p l i) /\
                  index (Valid?.tlss (verifier l)) i == 
                  index (Valid?.tlss (verifier (vlog_of_thread #p l i))) i)) 
        [SMTPat (vlog_of_thread #p l i)] = 
   let li = vlog_of_thread l i in
   let n = length l in
   if n = 0 then (
     admit ()
   )
   else admit()

(* 
 * the clock of a verifier thread at a particular position of the log
 *)
let clock_at_idx (#p:pos) (l:verifiable_log) 
                 (i:nat{i < p}) 
                 (j: seq_index (vlog_of_thread #p l i)): timestamp =
  let li = prefix (vlog_of_thread l i) j in
  let tls = index (Valid?.tlss (verifier li)) i in
  TLS?.clk tls

(* the clock of a verifier is monotonic *)
let lemma_clock_monotonic (#p:pos) (l:verifiable_log)
                          (i:nat{i < p})
                          (j:seq_index (vlog_of_thread #p l i)):
  Lemma (requires(j > 0))
        (ensures (clock_at_idx l i j `ts_leq` clock_at_idx l i (j - 1))) = admit()
 
let is_state_op (e:vlog_entry) = Get? e || Put? e

let to_state_op (e:vlog_entry{is_state_op e}): state_op = 
  match e with
  | Veritas.Verifier.Get k v -> Veritas.State.Get k v
  | Veritas.Verifier.Put k v -> Veritas.State.Put k v 

(*
let state_ops_by_thread (#p:pos) (l:vlog): ot: (seq (seq state_op)){length ot = p} = 
  let lt = vlog_by_thread #p l in
  let lt' = map (filter is_state_op) lt in
  map (map to_state_op) lt'

type hash_collision_union = 
  | Singleton: c:hash_collision -> hash_collision_union
  | MultiSet: c:ms_hash_collision -> hash_collision_union

let verifier_correct (#p:pos) (l:verifiable_log):
  Lemma (seq_consistent (state_ops_by_thread #p l) \/ hash_collision_union) = admit()
*)
