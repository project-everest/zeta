module Veritas.Verifier.Blum

open FStar.Seq
open Veritas.EAC
open Veritas.Interleave
open Veritas.Key
open Veritas.MultiSet
open Veritas.MultiSetHash
open Veritas.SeqAux
open Veritas.Verifier
open Veritas.Verifier.Global
open Veritas.Verifier.Thread
open Veritas.Verifier.TSLog

module E=Veritas.EAC
module I = Veritas.Interleave
module MS=Veritas.MultiSet
module MH=Veritas.MultiSetHash
module TL=Veritas.Verifier.TSLog
module VG = Veritas.Verifier.Global

(* sequence of blum adds in the time sequenced log *)
val ts_add_seq (itsl: its_log): seq ms_hashfn_dom

(* the addset in a time sequenced log *)
let ts_add_set (itsl: its_log): mset ms_hashfn_dom 
  = seq2mset (ts_add_seq itsl)

val lemma_add_elem_correct (itsl: its_log) (i: I.seq_index itsl):
  Lemma (requires (is_blum_add (I.index itsl i)))
        (ensures (contains (blum_add_elem (I.index itsl i)) (ts_add_set itsl)))

(* sequence of blum adds restricted to key k *)
val ts_add_seq_key (itsl: its_log) (k:key): seq ms_hashfn_dom

(* the addset restricted to key k *)
let ts_add_set_key (itsl: its_log) (k:key): mset ms_hashfn_dom
  = seq2mset (ts_add_seq_key itsl k)

(* the blum adds in the time sequenced log should be the same as global add set *)
val lemma_ts_add_set_correct (itsl: its_log): 
  Lemma (ts_add_set itsl == g_add_set (g_vlog_of itsl))

(* if the tail element is a blum add, then the add set is obtained by adding that 
 * blum add to the prefix *)
val lemma_ts_add_set_key_extend (itsl: its_log {I.length itsl > 0}):
  Lemma (requires (is_blum_add (I.telem itsl)))
        (ensures (ts_add_set_key itsl (key_of (I.index itsl (I.length itsl - 1))) == 
                  add_elem (ts_add_set_key (I.prefix itsl (I.length itsl - 1))
                                           (key_of (I.index itsl (I.length itsl - 1))))
                           (blum_add_elem (I.telem itsl))))

val lemma_ts_add_set_contains_add_elem (itsl: its_log) (i:I.seq_index itsl):
  Lemma (requires (is_blum_add (I.index itsl i)))
        (ensures (MS.contains (blum_add_elem (I.index itsl i)) (ts_add_set itsl)))

val lemma_ts_add_set_key_contains_only (itsl: its_log) (k:key) (be: ms_hashfn_dom):
  Lemma (requires (MS.contains be (ts_add_set_key itsl k)))
        (ensures (MH.key_of be = k))

val some_add_elem_idx (itsl: its_log) 
  (be: ms_hashfn_dom{MS.contains be (ts_add_set itsl)}): 
  (i:(I.seq_index itsl){is_blum_add (I.index itsl i) /\
                      be = blum_add_elem (I.index itsl i)})

(* get the blum evict element from an index *)
val blum_evict_elem (itsl: its_log) (i:I.seq_index itsl{is_evict_to_blum (I.index itsl i)}):
  (e:ms_hashfn_dom{MH.key_of e = key_of (I.index itsl i)})

val lemma_index_blum_evict_prefix (itsl: its_log) (i:nat{i <= I.length itsl}) (j:nat{j < i}):
  Lemma (requires (is_evict_to_blum (I.index itsl j)))
        (ensures (blum_evict_elem itsl j = blum_evict_elem (I.prefix itsl i) j))
        [SMTPat (blum_evict_elem (I.prefix itsl i) j)]


(* sequence of evicts in time sequence log *)
val ts_evict_seq (itsl: its_log): seq ms_hashfn_dom

(* set of evicts in time sequence log *)
let ts_evict_set (itsl: its_log): mset ms_hashfn_dom = 
  seq2mset (ts_evict_seq itsl)

(* the evict sequence restricted to key k *)
val ts_evict_seq_key (itsl: its_log) (k:key): seq ms_hashfn_dom

let ts_evict_set_key (itsl: its_log) (k:key): mset ms_hashfn_dom= 
  seq2mset (ts_evict_seq_key itsl k)

(* the blum evicts in time sequenced log should be the same as global evict set *)
val lemma_ts_evict_set_correct (itsl: its_log):
  Lemma (ts_evict_set itsl == g_evict_set (g_vlog_of itsl))

(* if the tail element is not an evict, the evict set is the same as the evict 
 * set of the length - 1 prefix 
 *)
val lemma_ts_evict_set_key_extend2 (itsl: its_log {I.length itsl > 0}):
  Lemma (requires (not (is_evict_to_blum (I.index itsl (I.length itsl - 1)))))
        (ensures (ts_evict_set_key itsl (key_of (I.index itsl (I.length itsl - 1))) == 
                  ts_evict_set_key (I.prefix itsl (I.length itsl - 1))
                                           (key_of (I.index itsl (I.length itsl - 1)))))

(* since evict_set is a pure set (not a multiset) we can identify the unique index 
 * for each element of the set *)
val index_blum_evict (itsl: its_log) (e: ms_hashfn_dom {contains e (ts_evict_set itsl)}):
  (i:I.seq_index itsl{is_evict_to_blum (I.index itsl i) /\ 
                    blum_evict_elem itsl i = e})

(* if the blum add occurs in the blum evict set, its index is earlier *)
val lemma_evict_before_add (itsl: its_log) (i:I.seq_index itsl{is_blum_add (I.index itsl i)}):
  Lemma (requires True)
        (ensures (not (contains (blum_add_elem (I.index itsl i)) (ts_evict_set itsl)) \/
                  index_blum_evict itsl (blum_add_elem (I.index itsl i)) < i))

(* a slightly different version of of the previous lemma - the count of an add element 
 * in the evict set is the same in the prefix as the full sequence *)
val lemma_evict_before_add2 (itsl: its_log) (i:I.seq_index itsl{is_blum_add (I.index itsl i)}):
   Lemma (requires True)
         (ensures (MS.mem (blum_add_elem (I.index itsl i)) (ts_evict_set itsl) =
                   MS.mem (blum_add_elem (I.index itsl i)) (ts_evict_set (I.prefix itsl i))))

val lemma_evict_before_add3 (itsl: its_log) (i: I.seq_index itsl) (j:I.seq_index itsl):
  Lemma (requires (is_blum_add (I.index itsl i) /\
                   is_evict_to_blum (I.index itsl j) /\
                   blum_add_elem (I.index itsl i) = blum_evict_elem itsl j))
        (ensures (j < i))

(* for an eac ts log, if the eac state of a key k is instore, the count of blum evicts 
 * is the same of blum adds for that key *)
val lemma_evict_add_count_same (itsl: TL.eac_log) (k:key):
  Lemma (requires (TL.is_eac_state_instore itsl k))
        (ensures (MS.size (ts_add_set_key itsl k) = MS.size (ts_evict_set_key itsl k)))

(* for an eac ts log, if the eac state of a key k is evicted to merkle, the count of blum evicts 
 * is the same of blum adds for that key *)
val lemma_evict_add_count_same_evictedm (itsl: TL.eac_log) (k:key):
  Lemma (requires (is_eac_state_evicted_merkle itsl k))
        (ensures (MS.size (ts_add_set_key itsl k) = MS.size (ts_evict_set_key itsl k)))

val lemma_mem_key_add_set_same (itsl: its_log) (be: ms_hashfn_dom):
  Lemma (mem be (ts_add_set itsl) = mem be (ts_add_set_key itsl (MH.key_of be)))

val lemma_mem_key_evict_set_same (itsl: its_log) (be: ms_hashfn_dom):
  Lemma (mem be (ts_evict_set itsl) = mem be (ts_evict_set_key itsl (MH.key_of be)))

(* the count of an element can only decrease in a prefix of itsl *)
val lemma_mem_monotonic (be:ms_hashfn_dom) (itsl: its_log) (i:nat{i <= I.length itsl}):
  Lemma (mem be (ts_evict_set itsl) >= mem be (ts_evict_set (I.prefix itsl i)) /\
         mem be (ts_add_set itsl) >= mem be (ts_add_set (I.prefix itsl i)))

(* the next add of a blum evict is a blum add of the same "element" *)
val lemma_blum_evict_add_same (itsl: TL.eac_log) (i:I.seq_index itsl):
  Lemma (requires (is_evict_to_blum (I.index itsl i) /\
                   TL.has_next_add_of_key itsl i (key_of (I.index itsl i))))
        (ensures (is_blum_add (I.index itsl (TL.next_add_of_key itsl i (key_of (I.index itsl i)))) /\
                  blum_evict_elem itsl i =                                   
                  blum_add_elem (I.index itsl (TL.next_add_of_key itsl i (key_of (I.index itsl i))))))

let to_blum_elem (s: eac_state{EACEvictedBlum? s}) (k:key): ms_hashfn_dom = 
  match s with
  | EACEvictedBlum v t j -> MHDom (k,v) t j

(* when the eac store is evicted, there exists a previous evict *)
val lemma_eac_evicted_blum_implies_previous_evict (itsl: its_log) (k:key):
  Lemma (requires (is_eac_state_evicted_blum itsl k))
        (ensures (has_some_entry_of_key itsl k /\
                  is_evict_to_blum (I.index itsl (last_idx_of_key itsl k)) /\
                  blum_evict_elem itsl (last_idx_of_key itsl k) = 
                  to_blum_elem (eac_state_of_key itsl k) k))

(* if we provide two indexes having the same add element then the membership of the element in the 
 * add set is at least two *)
val lemma_add_set_mem (itsl: its_log) (i: I.seq_index itsl) (j:I.seq_index itsl{j <> i}):
  Lemma (requires (is_blum_add (I.index itsl i) /\
                   is_blum_add (I.index itsl j) /\
                   blum_add_elem (I.index itsl i) = blum_add_elem (I.index itsl j)))
        (ensures (MS.mem (blum_add_elem (I.index itsl i)) (ts_add_set itsl) >= 2))
