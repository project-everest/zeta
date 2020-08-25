module Veritas.Verifier.Blum

open FStar.Seq
open Veritas.EAC
open Veritas.Interleave
open Veritas.Key
open Veritas.MultiSet
open Veritas.MultiSetHash
open Veritas.SeqAux
open Veritas.Verifier
open Veritas.Verifier.CorrectDefs
open Veritas.Verifier.TSLog

module E=Veritas.EAC
module MS=Veritas.MultiSet
module MH=Veritas.MultiSetHash
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

(* get the blum add element from an index *)
let blum_add_elem (#p:nat) (ie:idx_elem #vlog_entry p{is_blum_add ie}):
  ms_hashfn_dom = 
  let (e,_) = ie in
  match e with
  | AddB r t j -> MHDom r t j

(* sequence of blum adds in the time sequenced log *)
let ts_add_seq (#n:pos) (itsl: its_log n): seq ms_hashfn_dom =
  map blum_add_elem (filter_refine is_blum_add itsl)

(* the addset in a time sequenced log *)
let ts_add_set (#n:pos) (itsl: its_log n): mset ms_hashfn_dom 
  = seq2mset (ts_add_seq itsl)

val lemma_add_elem_correct (#n:pos) (itsl: its_log n) (i:seq_index itsl{is_blum_add (index itsl i)}):
  Lemma (requires (is_blum_add (index itsl i)))
        (ensures (contains (blum_add_elem (index itsl i)) (ts_add_set itsl)))

(* sequence of blum adds restricted to key k *)
val ts_add_seq_key (#n:pos) (itsl: its_log n) (k:key): seq ms_hashfn_dom

(* the addset restricted to key k *)
let ts_add_set_key (#n:pos) (itsl: its_log n) (k:key): mset ms_hashfn_dom
  = seq2mset (ts_add_seq_key itsl k)

(* the blum adds in the time sequenced log should be the same as global add set *)
val lemma_ts_add_set_correct (#n:pos) (itsl: its_log n): 
  Lemma (ts_add_set itsl == g_add_set (partition_idx_seq itsl))

(* if the tail element is a blum add, then the add set is obtained by adding that 
 * blum add to the prefix *)
val lemma_ts_add_set_key_extend (#n:pos) (itsl: its_log n {length itsl > 0}):
  Lemma (requires (is_blum_add (telem itsl)))
        (ensures (ts_add_set_key itsl (key_of (index itsl (length itsl - 1))) == 
                  add_elem (ts_add_set_key (its_prefix itsl (length itsl - 1))
                                           (key_of (index itsl (length itsl - 1))))
                           (blum_add_elem (telem itsl))))

(* get the blum evict element from an index *)
val blum_evict_elem (#p:pos) (itsl: its_log p) (i:seq_index itsl{is_blum_evict (index itsl i)}):
  (e:ms_hashfn_dom{MH.key_of e = TL.key_of (index itsl i)})

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

(* if the tail element is not an evict, the evict set is the same as the evict 
 * set of the length - 1 prefix 
 *)
val lemma_ts_evict_set_key_extend2 (#n:pos) (itsl: its_log n {length itsl > 0}):
  Lemma (requires (not (is_blum_evict (index itsl (length itsl - 1)))))
        (ensures (ts_evict_set_key itsl (key_of (index itsl (length itsl - 1))) == 
                  ts_evict_set_key (its_prefix itsl (length itsl - 1))
                                           (key_of (index itsl (length itsl - 1)))))

(* since evict_set is a pure set (not a multiset) we can identify the unique index 
 * for each element of the set *)
val index_blum_evict (#p:pos) (itsl: its_log p) (e: ms_hashfn_dom {contains e (ts_evict_set itsl)}):
  (i:seq_index itsl{is_blum_evict (index itsl i) /\ 
                    blum_evict_elem itsl i = e})

(* if the blum add occurs in the blum evict set, its index is earlier *)
val lemma_evict_before_add (#p:pos) (itsl: its_log p) (i:seq_index itsl{is_blum_add (index itsl i)}):
  Lemma (requires True)
        (ensures (not (contains (blum_add_elem (index itsl i)) (ts_evict_set itsl)) \/
                  index_blum_evict itsl (blum_add_elem (index itsl i)) < i))

(* a slightly different version of of the previous lemma - the count of an add element 
 * in the evict set is the same in the prefix as the full sequence *)
val lemma_evict_before_add2 (#p:pos) (itsl: its_log p) (i:seq_index itsl{is_blum_add (index itsl i)}):
   Lemma (requires True)
         (ensures (MS.mem (blum_add_elem (index itsl i)) (ts_evict_set itsl) =
                   MS.mem (blum_add_elem (index itsl i)) (ts_evict_set (its_prefix itsl i))))

(* for an eac ts log, if the eac state of a key k is instore, the count of blum evicts 
 * is the same of blum adds for that key *)
val lemma_evict_add_count_same (#p:pos) (itsl: eac_ts_log p) (k:key):
  Lemma (requires (is_eac_state_instore itsl k))
        (ensures (MS.size (ts_add_set_key itsl k) = MS.size (ts_evict_set_key itsl k)))

(* for an eac ts log, if the eac state of a key k is evicted to merkle, the count of blum evicts 
 * is the same of blum adds for that key *)
val lemma_evict_add_count_same_evictedm (#p:pos) (itsl: eac_ts_log p) (k:key):
  Lemma (requires (is_eac_state_evicted_merkle itsl k))
        (ensures (MS.size (ts_add_set_key itsl k) = MS.size (ts_evict_set_key itsl k)))

val lemma_mem_key_add_set_same (#p:pos) (itsl: eac_ts_log p) (be: ms_hashfn_dom):
  Lemma (mem be (ts_add_set itsl) = mem be (ts_add_set_key itsl (MH.key_of be)))

val lemma_mem_key_evict_set_same (#p:pos) (itsl: eac_ts_log p) (be: ms_hashfn_dom):
  Lemma (mem be (ts_evict_set itsl) = mem be (ts_evict_set_key itsl (MH.key_of be)))

(* the count of an element can only decrease in a prefix of itsl *)
val lemma_mem_monotonic (#p:pos) (be:ms_hashfn_dom) (itsl: eac_ts_log p) (i:nat{i < length itsl}):
  Lemma (mem be (ts_evict_set itsl) >= mem be (ts_evict_set (its_prefix itsl i)) /\
         mem be (ts_add_set itsl) >= mem be (ts_add_set (its_prefix itsl i)))

(* the next add of a blum evict is a blum add of the same "element" *)
val lemma_blum_evict_add_same (#p:pos) (itsl: eac_ts_log p) (i:seq_index itsl):
  Lemma (requires (TL.is_blum_evict (index itsl i) /\
                   TL.has_next_add_of_key itsl i (TL.key_of (index itsl i))))
        (ensures (TL.is_blum_add (index itsl (TL.next_add_of_key itsl i (TL.key_of (index itsl i)))) /\
                  blum_evict_elem itsl i =                                   
                  blum_add_elem (index itsl (TL.next_add_of_key itsl i (TL.key_of (index itsl i))))))

let to_blum_elem (s: eac_state{EACEvictedBlum? s}) (k:key): ms_hashfn_dom = 
  match s with
  | EACEvictedBlum v t j -> MHDom (k,v) t j

(* when the eac store is evicted, there exists a previous evict *)
val lemma_eac_evicted_blum_implies_previous_evict (#p:pos) (itsl: its_log p) (k:key):
  Lemma (requires (is_eac_state_evicted_blum itsl k))
        (ensures (has_some_entry_of_key itsl k /\
                  is_blum_evict (index itsl (last_idx_of_key itsl k)) /\
                  blum_evict_elem itsl (last_idx_of_key itsl k) = 
                  to_blum_elem (eac_state_of_key itsl k) k))
