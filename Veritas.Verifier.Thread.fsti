module Veritas.Verifier.Thread

open Veritas.MultiSetHash
open Veritas.SeqAux
open Veritas.Verifier

module S = FStar.Seq
module SA = Veritas.SeqAux
module V = Veritas.Verifier

(*
 * an indexed vlog attaches an nat index to a vlog
 * indicating the id of the verifier thread processing
 * the log
 *)
let thread_id_vlog = thread_id & vlog

(* thread id of the indexed vlog *)
let thread_id_of (tl: thread_id_vlog): nat = fst tl

(* vlog of an indexed vlog *)
let vlog_of (tl: thread_id_vlog): vlog = snd tl

let length (tl: thread_id_vlog): nat =
  S.length (vlog_of tl)

let idx (tl: thread_id_vlog) = i:nat{i < length tl}

let index (tl: thread_id_vlog) (i:idx tl): vlog_entry =
  S.index (vlog_of tl) i

let append1 (tl: thread_id_vlog) (e: vlog_entry): thread_id_vlog =
  (thread_id_of tl), (SA.append1 (vlog_of tl) e)

let prefix (tl: thread_id_vlog) (i:nat{i <= length tl}): thread_id_vlog =
  (thread_id_of tl), (SA.prefix (vlog_of tl) i)

let verify (tl:thread_id_vlog): V.vtls =
  t_verify (thread_id_of tl) (vlog_of tl)

let verifiable (tl: thread_id_vlog): bool =
  Valid? (verify tl)

let verifiable_log = tl: thread_id_vlog {verifiable tl}

(* if a thread log is verifiable, its prefix is verifiable *)
val lemma_verifiable_implies_prefix_verifiable
  (tl:verifiable_log) (i:nat{i <= length tl}):
  Lemma (requires (True))
        (ensures (verifiable (prefix tl i)))
        [SMTPat (prefix tl i)]

(* clock after processing the i'th entry *)
let clock (tl:verifiable_log) (i:idx tl): timestamp =
  Valid?.clk (verify (prefix tl (i + 1)))

(* clock is monotonic *)
val lemma_clock_monotonic (tl: verifiable_log) (i:idx tl) (j:idx tl{j >= i}): 
  Lemma (clock tl i `ts_leq` clock tl j)

(* the thread id in the state is always the one specified in the parameter *)
val lemma_thread_id_state (tl: verifiable_log):
  Lemma (V.thread_id_of (verify tl) = thread_id_of tl)

(* these log entries require the store contain the key_of e, otherwise result in a failure *)
let requires_key_in_store (e:vlog_entry): bool = 
  match e with
  | Get _ _ -> true
  | Put _ _ -> true
  | EvictM _ _ -> true
  | EvictB _ _ -> true
  | EvictBM _ _ _ -> true
  | _ -> false

(* the store after processing a log *)
let store (tl:verifiable_log): vstore = 
  Valid?.st (verify tl)

(* the store after processing i entries *)
let store_idx (tl: verifiable_log) (i: idx tl): vstore = 
  store (prefix tl i)

(* 
 * if the (i+1)'th entry requires the key to be in the store, then the verifier store 
 * contains the key after processing i entries 
 *)
val lemma_requires_key_in_store 
  (tl: verifiable_log) 
  (i:idx tl{requires_key_in_store (index tl i)}):
  Lemma (store_contains (store_idx tl i) (V.key_of (index tl i)))


