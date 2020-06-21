module Veritas.Verifier.Correctness

open FStar.Seq
open Veritas.Key
open Veritas.MultiSetHash
open Veritas.Record
open Veritas.Verifier
open Veritas.SeqAux

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
        (decreases (length l)) =
  let n = length l in
  if n = 0 then ()
  else if i = n then ()
  else
    lemma_verifiable_implies_prefix_verifiable #p (prefix l (n - 1)) i

(* TODO: #p seems to prevent the use of SMTPat in lemma above *)
let vprefix (#p:pos) (l:verifiable_log #p) (i:nat{i <= length l}): 
  l':(verifiable_log #p){l' = prefix l i} = 
  lemma_verifiable_implies_prefix_verifiable l i;
  prefix l i

(* is this a thread-local operation *)
let is_thread_op (e:vlog_entry_g) = TOp? e

(* is the operator at index i a thread-local op *)
let is_thread_op_idx (l:vlog) (i:vl_index l) = 
  is_thread_op (index l i)

(* thread id of a thread-local op *)
let thread_id_of (e:vlog_entry_g {is_thread_op e}) = 
  TOp?.tid e

let thread_id_of_idx (l:vlog) (i:vl_index l{is_thread_op_idx l i}) = 
  thread_id_of (index l i)

(* thread id of every thread-local op < p (verifier parallelism) *)
let lemma_thread_id_valid (#p:pos) 
                          (l:verifiable_log #p) 
                          (i:vl_index l {is_thread_op_idx l i})
  : Lemma (thread_id_of_idx l i < p) = 
  let l' = vprefix l i in
  let l'' = vprefix l (i + 1) in
  ()
         
(* 
 * we associate a timestamp to every thread-local op based on the 
 * thread clock after the completion of the operation 
 *)
let op_clock (#p:pos) 
             (l:verifiable_log #p) 
             (i:vl_index l {is_thread_op_idx l i}): timestamp = 
 let l' = vprefix l (i + 1) in
 let vs = verifier #p l' in
 let ti = thread_id_of_idx l i in
 lemma_thread_id_valid l i;
 thread_clock ti vs

(* thread-local log: a log with only thread-local operations (no VerifyEpoch) *)
type thread_local_log (l:vlog) = forall (i:vl_index l). {:pattern (is_thread_op_idx l i)} is_thread_op_idx l i

type tl_log (#p:pos) = l:(verifiable_log #p){thread_local_log l}

(* a thread-local log is clock-ordered is the clock of each operation is monotonically increasing *)
type clock_ordered_log (#p:pos) (l:tl_log #p) = 
  forall (i:vl_index l). i > 0 ==> (op_clock l i `ts_geq` op_clock l (i - 1))

type co_log (#p:pos) = l:(tl_log #p){clock_ordered_log l}

(* the key referenced by an log operation *)
let key_of (e:vlog_entry) = 
  match e with
  | Get k _ -> k
  | Put k _ -> k
  | AddM r _ -> let (k,_) = r in k
  | EvictM k _ -> k
  | AddB r _ _ -> let (k,_) = r in k
  | EvictB k _ -> k
  | EvictBM k _ _ -> k

