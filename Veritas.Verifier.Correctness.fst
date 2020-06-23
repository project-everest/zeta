module Veritas.Verifier.Correctness

open FStar.Seq
open Veritas.Key
open Veritas.MultiSetHash
open Veritas.Record
open Veritas.Verifier
open Veritas.SeqAux
open Veritas.SeqOps

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

let thread_id (#p:pos) (e: vlog_entry_g #p) = TOp?.tid e

let thread_id_idx (#p:pos) (l:vlog) (i:vl_index l) = thread_id #p (index l i)

let partition_vlog (#p:pos) (l:vlog) = partition #(vlog_entry_g #p) #p l (thread_id #p) 
