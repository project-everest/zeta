module Veritas.Verifier.Blum

open FStar.Seq
open Veritas.Interleave
open Veritas.Key
open Veritas.MultiSet
open Veritas.MultiSetHash
open Veritas.SeqAux
open Veritas.Verifier
open Veritas.Verifier.CorrectDefs
open Veritas.Verifier.TSLog

module M=Veritas.MultiSetHash
module TL=Veritas.Verifier.TSLog

(* global add sequence *)
val g_add_seq (gl: g_verifiable_log): seq (ms_hashfn_dom)

(* multiset derived from all the blum adds in gl *)
let g_add_set (gl: g_verifiable_log): mset ms_hashfn_dom =
  seq2mset (g_add_seq gl)

(* the hadd that the verifier computes is the multiset hash of all the adds *)
val lemma_g_hadd_correct (gl: g_verifiable_log):
  Lemma (g_hadd gl = ms_hashfn (g_add_seq gl))

(* a single sequence containing all the blum evicts *)
val g_evict_seq (gl: g_verifiable_log): seq ms_hashfn_dom 

let g_evict_set (gl: g_verifiable_log): mset ms_hashfn_dom = 
  seq2mset (g_evict_seq gl)

(* the global evict set is a set (not a multiset) *)
val g_evict_set_is_set (gl: g_verifiable_log): 
  Lemma (is_set (g_evict_set gl))

val lemma_ghevict_correct (gl: g_verifiable_log):
  Lemma (g_hevict gl = ms_hashfn (g_evict_seq gl))

(* is the i'th index of itsl a blum add *)
let is_blum_add (#p:nat) (ie:idx_elem #vlog_entry p):bool =
  let (e,_) = ie in
  match e with
  | AddB _ _ _ -> true
  | _ -> false

(* get the blum add element from an index *)
let blum_add_elem (#p:nat) (ie:idx_elem #vlog_entry p{is_blum_add ie}):
  ms_hashfn_dom = 
  let (e,_) = ie in
  match e with
  | AddB r t j -> MHDom r t j

(* sequence of blum adds in the time sequenced log *)
val ts_add_seq (#n:pos) (itsl: its_log n): seq ms_hashfn_dom

(* the addset in a time sequenced log *)
let ts_add_set (#n:pos) (itsl: its_log n): mset ms_hashfn_dom 
  = seq2mset (ts_add_seq itsl)

(* sequence of blum adds restricted to key k *)
val ts_add_seq_key (#n:pos) (itsl: its_log n) (k:key): seq ms_hashfn_dom

(* the addset restricted to key k *)
let ts_add_set_key (#n:pos) (itsl: its_log n) (k:key): mset ms_hashfn_dom
  = seq2mset (ts_add_seq_key itsl k)

(* the blum adds in the time sequenced log should be the same as global add set *)
val lemma_ts_add_set_correct (#n:pos) (itsl: its_log n): 
  Lemma (ts_add_set itsl == g_add_set (partition_idx_seq itsl))

(* is the index i of ts log an blum evict *)
val is_blum_evict (#p:pos) (itsl: its_log p) (i: seq_index itsl): bool

(* get the blum evict element from an index *)
val blum_evict_elem (#p:pos) (itsl: its_log p) (i:seq_index itsl{is_blum_evict itsl i}):
  (e:ms_hashfn_dom{M.key_of e = TL.key_of itsl i})

(* sequence of evicts in time sequence log *)
val ts_evict_seq (#n:pos) (itsl: its_log n): seq ms_hashfn_dom

(* set of evicts in time sequence log *)
let ts_evict_set (#n:pos) (itsl: its_log n): mset ms_hashfn_dom = 
  seq2mset (ts_evict_seq itsl)

(* the evict sequence restricted to key k *)
val ts_evict_seq_key (#n:pos) (itsl: its_log n) (k:key): seq ms_hashfn_dom

let ts_evict_set_key (#n:pos) (itsl: its_log n) (k:key): mset ms_hashfn_dom= 
  seq2mset (ts_evict_seq_key itsl k)

(* the blum evicts in time sequenced log should be the same as global evict set *)
val lemma_ts_evict_set_correct (#n:pos) (itsl: its_log n):
  Lemma (ts_evict_set itsl == g_evict_set (partition_idx_seq itsl))

(* since evict_set is a pure set (not a multiset) we can identify the unique index 
 * for each element of the set *)
val index_blum_evict (#p:pos) (itsl: its_log p) (e: ms_hashfn_dom {contains e (ts_evict_set itsl)}):
  (i:seq_index itsl{is_blum_evict itsl i /\ 
                    blum_evict_elem itsl i = e})

(* if the blum add occurs in the blum evict set, its index is earlier *)
val lemma_evict_before_add (#p:pos) (itsl: its_log p) (i:seq_index itsl{is_blum_add (index itsl i)}):
  Lemma (requires True)
        (ensures (not (contains (blum_add_elem (index itsl i)) (ts_evict_set itsl)) \/
                  index_blum_evict itsl (blum_add_elem (index itsl i)) < i))
         
