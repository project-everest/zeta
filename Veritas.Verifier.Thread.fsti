module Veritas.Verifier.Thread

open Veritas.MultiSetHash
open Veritas.SeqAux
open Veritas.Verifier

module S = FStar.Seq
module SA = Veritas.SeqAux
module V = Veritas.Verifier
module MH = Veritas.MultiSetHash

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
let store_at (tl: verifiable_log) (i: idx tl): vstore = 
  store (prefix tl i)

(* the verifier state after processing i entries *)
let state_at (tl: verifiable_log) (i:nat{i <= length tl}): st:vtls{Valid? st} =
  (verify (prefix tl i))

(* the state after processing i'th entry is obtained by applying the verify 
 * step to the state before processing the i'th entry *)
val lemma_state_transition (tl: verifiable_log) (i: idx tl): 
  Lemma (state_at tl (i + 1) == 
         t_verify_step (state_at tl i) (index tl i))

(* 
 * if the (i+1)'th entry requires the key to be in the store, then the verifier store 
 * contains the key after processing i entries 
 *)
val lemma_requires_key_in_store 
  (tl: verifiable_log) 
  (i:idx tl{requires_key_in_store (index tl i)}):
  Lemma (store_contains (store_at tl i) (V.key_of (index tl i)))


(* get the blum add element from an index *)
let blum_add_elem (e:vlog_entry {is_blum_add e}):
  ms_hashfn_dom = 
  match e with
  | AddB r t j -> MHDom r t j

val blum_add_seq (tl: verifiable_log): S.seq ms_hashfn_dom

val add_seq_map (tl: verifiable_log) (i: idx tl{is_blum_add (index tl i)}):
  (j: SA.seq_index (blum_add_seq tl){S.index (blum_add_seq tl) j =
                                     blum_add_elem (index tl i)})

val add_seq_inv_map (tl: verifiable_log) (j: SA.seq_index (blum_add_seq tl)):
  (i: idx tl {is_blum_add (index tl i) /\
              blum_add_elem (index tl i) = S.index (blum_add_seq tl) j /\
              add_seq_map tl i = j})

val lemma_add_seq_inv (tl: verifiable_log) (i: idx tl{is_blum_add (index tl i)}):
  Lemma (requires True)
        (ensures (add_seq_inv_map tl (add_seq_map tl i) = i))
        [SMTPat (add_seq_map tl i)]

let hadd (tl: verifiable_log): ms_hash_value = 
  Valid?.hadd (verify tl)

val lemma_hadd_correct (tl: verifiable_log):
  Lemma (hadd tl = ms_hashfn (blum_add_seq tl))

val blum_evict_elem (tl: verifiable_log) (i:idx tl{is_evict_to_blum (index tl i)}): ms_hashfn_dom

val blum_evict_seq (tl: verifiable_log): S.seq ms_hashfn_dom

let hevict (tl: verifiable_log): ms_hash_value = 
  Valid?.hevict (verify tl)

val lemma_hevict_correct (tl: verifiable_log):
  Lemma (hevict tl = ms_hashfn (blum_evict_seq tl))

(* all elements of tl's blum_evict_seq contain tid of tl *)
val lemma_evict_elem_tid (tl: verifiable_log):
  Lemma (all (is_of_thread_id (thread_id_of tl)) (blum_evict_seq tl))
  
val lemma_evict_elem_unique (tl: verifiable_log) (i1 i2: SA.seq_index (blum_evict_seq tl)):
  Lemma (i1 <> i2 ==> S.index (blum_evict_seq tl) i1 <> S.index (blum_evict_seq tl) i2)

val evict_seq_map (tl: verifiable_log) (i: idx tl{is_evict_to_blum (index tl i)}):
  (j: SA.seq_index (blum_evict_seq tl) {S.index (blum_evict_seq tl) j = 
                                        blum_evict_elem tl i})

val evict_seq_inv_map (tl: verifiable_log) (j: SA.seq_index (blum_evict_seq tl)):
  (i: idx tl{is_evict_to_blum (index tl i) /\
             blum_evict_elem tl i = S.index (blum_evict_seq tl) j /\
             evict_seq_map tl i = j})

val lemma_evict_seq_inv (tl: verifiable_log) (i: idx tl{is_evict_to_blum (index tl i)}):
  Lemma (requires True)
        (ensures (evict_seq_inv_map tl (evict_seq_map tl i) = i))
        [SMTPat (evict_seq_map tl i)]

val lemma_blum_evict_elem_key (tl: verifiable_log) (i: idx tl{is_evict_to_blum (index tl i)}):
  Lemma (MH.key_of (blum_evict_elem tl i) = V.key_of (index tl i))
