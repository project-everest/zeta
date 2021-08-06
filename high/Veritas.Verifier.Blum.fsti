module Veritas.Verifier.Blum

open FStar.Seq
open Veritas.EAC
open Veritas.Interleave
open Veritas.Key
open Veritas.MultiSet
open Veritas.MultiSetHash
open Veritas.MultiSetHashDomain
open Veritas.SeqAux
open Veritas.Verifier
open Veritas.Verifier.Global
open Veritas.Verifier.Thread
open Veritas.Verifier.TSLog

module S = FStar.Seq
module SA = Veritas.SeqAux
module E=Veritas.EAC
module I = Veritas.Interleave
module MS=Veritas.MultiSet
module MH=Veritas.MultiSetHash
module TL=Veritas.Verifier.TSLog
module VG = Veritas.Verifier.Global

(* sequence of blum adds in the time sequenced log belonging to epoch ep *)
val ts_add_seq (ep: epoch) (itsl: its_log): seq ms_hashfn_dom

(* the addset in a time sequenced log *)
let ts_add_set (ep: epoch) (itsl: its_log): mset_ms_hashfn_dom
  = seq2mset #_ #ms_hashfn_dom_cmp (ts_add_seq ep itsl)

val lemma_add_elem_correct (itsl: its_log) (i: I.seq_index itsl):
  Lemma (requires (is_blum_add (I.index itsl i)))
        (ensures (let e = I.index itsl i in
                  let be = blum_add_elem e in
                  let ep = MH.epoch_of be in
                  ts_add_set ep itsl `MS.contains` be))

(* sequence of blum adds in epoch ep restricted to key k *)
val ts_add_seq_key (ep: epoch) (itsl: its_log) (k:key): seq ms_hashfn_dom

(* the addset restricted to key k *)
let ts_add_set_key (ep: epoch) (itsl: its_log) (k:key): mset_ms_hashfn_dom
  = seq2mset #_ #ms_hashfn_dom_cmp (ts_add_seq_key ep itsl k)

(* the blum adds in the time sequenced log should be the same as global add set *)
val lemma_ts_add_set_correct (ep: epoch) (itsl: its_log):
  Lemma (ts_add_set ep itsl == g_add_set ep (g_vlog_of itsl))

(* the epoch of every element in the add-set of an epoch ep is ep *)
val lemma_ts_add_set_epoch_correct (ep: epoch) (itsl: its_log) (be: ms_hashfn_dom):
  Lemma (requires (ts_add_set ep itsl `MS.contains` be))
  (ensures (MH.epoch_of be = ep))

(* if the tail element is a blum add, then the add set is obtained by adding that 
 * blum add to the prefix *)
val lemma_ts_add_set_key_extend (itsl: its_log {I.length itsl > 0}):
  Lemma (requires (is_blum_add (I.telem itsl)))
        (ensures (let e = I.telem itsl in
                  let k = key_of e in
                  let be = blum_add_elem e in
                  let ep = MH.epoch_of be in
                  let n = I.length itsl in
                  let itsl' = I.prefix itsl (n - 1) in
                  ts_add_set_key ep itsl k ==
                  add_elem (ts_add_set_key ep itsl' k) be))

val some_add_elem_idx (ep: epoch) (itsl: its_log)
  (be: ms_hashfn_dom{ts_add_set ep itsl `MS.contains` be}):
  (i:(I.seq_index itsl){is_blum_add (I.index itsl i) /\
                      be = blum_add_elem (I.index itsl i)})

val lemma_ts_add_set_key_contains_only (ep: epoch) (itsl: its_log) (k:key) (be: ms_hashfn_dom):
  Lemma (requires (ts_add_set_key ep itsl k `MS.contains` be))
        (ensures (MH.key_of be = k))

val lemma_ts_add_set_key_epoch_correct (ep: epoch) (itsl: its_log) (be: ms_hashfn_dom):
  Lemma (requires (let k = MH.key_of be in
                   ts_add_set_key ep itsl k `MS.contains` be))
        (ensures (let k = MH.key_of be in
                  MH.epoch_of be = ep))

(* get the blum evict element from an index *)
let blum_evict_elem (itsl: its_log) (i:I.seq_index itsl{is_evict_to_blum (I.index itsl i)}):
  (e:ms_hashfn_dom{MH.key_of e = key_of (I.index itsl i)}) = TL.blum_evict_elem itsl i

val lemma_index_blum_evict_prefix (itsl: its_log) (i:nat{i <= I.length itsl}) (j:nat{j < i}):
  Lemma (requires (is_evict_to_blum (I.index itsl j)))
        (ensures (blum_evict_elem itsl j = blum_evict_elem (I.prefix itsl i) j))
        [SMTPat (blum_evict_elem (I.prefix itsl i) j)]

(* sequence of evicts in time sequence log *)
val ts_evict_seq (ep: epoch) (itsl: its_log): seq ms_hashfn_dom

(* set of evicts in time sequence log *)
let ts_evict_set (ep: epoch) (itsl: its_log): mset_ms_hashfn_dom =
  seq2mset #_ #ms_hashfn_dom_cmp (ts_evict_seq ep itsl)

(* the evict sequence restricted to key k *)
val ts_evict_seq_key (ep: epoch) (itsl: its_log) (k:key): seq ms_hashfn_dom

let ts_evict_set_key (ep: epoch) (itsl: its_log) (k:key): mset_ms_hashfn_dom=
  seq2mset #_ #ms_hashfn_dom_cmp (ts_evict_seq_key ep itsl k)

(* the blum evicts in time sequenced log should be the same as global evict set *)
val lemma_ts_evict_set_correct (ep: epoch) (itsl: its_log):
  Lemma (ts_evict_set ep itsl == g_evict_set ep (g_vlog_of itsl))

(* the epoch of every element in the add-set of an epoch ep is ep *)
val lemma_ts_evict_set_epoch_correct (ep: epoch) (itsl: its_log) (be: ms_hashfn_dom):
  Lemma (requires (ts_evict_set ep itsl `MS.contains` be))
  (ensures (MH.epoch_of be = ep))

(* if the tail element is not an evict, the evict set is the same as the evict 
 * set of the length - 1 prefix 
 *)
val lemma_ts_evict_set_key_extend2 (ep: epoch) (itsl: its_log {I.length itsl > 0}):
  Lemma (requires (not (is_evict_to_blum (I.index itsl (I.length itsl - 1)))))
        (ensures (let n = I.length itsl in
                  let itsl' = I.prefix itsl (n - 1) in
                  let e = I.index itsl (n - 1) in
                  let k = key_of e in
                  ts_evict_set_key ep itsl k ==
                  ts_evict_set_key ep itsl' k))

(* since evict_set is a pure set (not a multiset) we can identify the unique index 
 * for each element of the set *)
val index_blum_evict (ep: epoch) (itsl: its_log) (e: ms_hashfn_dom {ts_evict_set ep itsl `contains` e}):
  (i:I.seq_index itsl{is_evict_to_blum (I.index itsl i) /\ 
                    blum_evict_elem itsl i = e})

(* if the blum add occurs in the blum evict set, its index is earlier *)
val lemma_evict_before_add (itsl: its_log) (i:I.seq_index itsl{is_blum_add (I.index itsl i)}):
  Lemma (ensures (let e = I.index itsl i in
                  let be = blum_add_elem e in
                  let ep = MH.epoch_of be in
                  not (ts_evict_set ep itsl `contains` be) \/
                  index_blum_evict ep itsl be < i))

(* a slightly different version of of the previous lemma - the count of an add element 
 * in the evict set is the same in the prefix as the full sequence *)
val lemma_evict_before_add2 (itsl: its_log) (i:I.seq_index itsl{is_blum_add (I.index itsl i)}):
   Lemma (ensures (let e = I.index itsl i in
                   let be = blum_add_elem e in
                   let ep = MH.epoch_of be in
                   MS.mem be (ts_evict_set ep itsl) =
                   MS.mem be (ts_evict_set ep (I.prefix itsl i))))

val lemma_evict_before_add3 (itsl: its_log) (i: I.seq_index itsl) (j:I.seq_index itsl):
  Lemma (requires (is_blum_add (I.index itsl i) /\
                   is_evict_to_blum (I.index itsl j) /\
                   blum_add_elem (I.index itsl i) = blum_evict_elem itsl j))
        (ensures (j < i))

(* for an eac ts log, if the eac state of a key k is instore, the count of blum evicts 
 * is the same of blum adds for that key for any epoch *)
val lemma_evict_add_count_same (ep: epoch) (itsl: TL.eac_log) (k:key):
  Lemma (requires (TL.is_eac_state_instore itsl k))
        (ensures (MS.size (ts_add_set_key ep itsl k) = MS.size (ts_evict_set_key ep itsl k)))

(* for an eac ts log, if the eac state of a key k is evicted to merkle, the count of blum evicts 
 * is the same of blum adds for that key *)
val lemma_evict_add_count_same_evictedm (ep: epoch) (itsl: TL.eac_log) (k:key):
  Lemma (requires (is_eac_state_evicted_merkle itsl k))
        (ensures (MS.size (ts_add_set_key ep itsl k) = MS.size (ts_evict_set_key ep itsl k)))

val lemma_mem_key_add_set_same (itsl: its_log) (be: ms_hashfn_dom):
  Lemma (let ep = MH.epoch_of be in
         mem be (ts_add_set ep itsl) = mem be (ts_add_set_key ep itsl (MH.key_of be)))

val lemma_mem_key_evict_set_same (itsl: its_log) (be: ms_hashfn_dom):
  Lemma (let ep = MH.epoch_of be in
         mem be (ts_evict_set ep itsl) = mem be (ts_evict_set_key ep itsl (MH.key_of be)))

(* the count of an element can only decrease in a prefix of itsl *)
val lemma_mem_monotonic (be:ms_hashfn_dom) (itsl: its_log) (i:nat{i <= I.length itsl}):
  Lemma (let ep = MH.epoch_of be in
         mem be (ts_evict_set ep itsl) >= mem be (ts_evict_set ep (I.prefix itsl i)) /\
         mem be (ts_add_set ep itsl) >= mem be (ts_add_set ep (I.prefix itsl i)))

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
val lemma_eac_evicted_blum_implies_previous_evict (itsl: TL.eac_log) (k:key):
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
        (ensures (let be = blum_add_elem (I.index itsl i) in
                  let ep = MH.epoch_of be in
                  MS.mem (blum_add_elem (I.index itsl i)) (ts_add_set ep itsl) >= 2))

val eac_instore_addb_diff_elem (itsl: its_log)
                               (i: I.seq_index itsl{let itsli = I.prefix itsl i in
                                                    let e = I.index itsl i in
                                                    is_blum_add e /\
                                                    TL.is_eac itsli /\
                                                    (let k = key_of e in
                                                     TL.is_eac_state_instore itsli k)})
  : (be':ms_hashfn_dom{let itsli' = I.prefix itsl (i+1) in
                       let ep = MH.epoch_of be' in
                       let as = ts_add_set ep itsli' in
                       let es = ts_evict_set ep itsli' in
                       let be = blum_add_elem (I.index itsl i) in
                       MS.mem be' as > MS.mem be' es /\
                       epoch_of be = epoch_of be'})

val eac_evictedm_addb_diff_elem (itsl: its_log) 
                               (i: I.seq_index itsl{let itsli = I.prefix itsl i in
                                                    let e = I.index itsl i in
                                                    is_blum_add e /\
                                                    TL.is_eac itsli /\
                                                    (let k = key_of e in
                                                     TL.is_eac_state_evicted_merkle itsli k)})
  : (be':ms_hashfn_dom{let itsli' = I.prefix itsl (i+1) in
                       let ep = MH.epoch_of be' in
                       let as = ts_add_set ep itsli' in
                       let es = ts_evict_set ep itsli' in
                       let be = blum_add_elem (I.index itsl i) in
                       MS.mem be' as > MS.mem be' es /\
                       epoch_of be = epoch_of be'})

val eac_evictedb_addb_diff_elem (itsl: its_log) 
                               (i: I.seq_index itsl{let itsli = I.prefix itsl i in
                                                    let itsli' = I.prefix itsl (i + 1) in
                                                    let e = I.index itsl i in
                                                    is_blum_add e /\
                                                    TL.is_eac itsli /\
                                                    not (TL.is_eac itsli') /\
                                                    (let k = key_of e in
                                                     TL.is_eac_state_evicted_blum itsli k)})
  : (be':ms_hashfn_dom{let itsli' = I.prefix itsl (i+1) in
                       let ep = MH.epoch_of be' in
                       let as = ts_add_set ep itsli' in
                       let es = ts_evict_set ep itsli' in
                       let be = blum_add_elem (I.index itsl i) in
                       MS.mem be' as > MS.mem be' es /\
                       epoch_of be = epoch_of be'})

val eac_add_set_mem_atleast_evict_set_mem (itsl: TL.eac_log) (be: ms_hashfn_dom) (tid: valid_tid itsl):
  Lemma (requires (let k = MH.key_of be in
                   store_contains (TL.thread_store itsl tid) k))
        (ensures (let ep = MH.epoch_of be in
                  MS.mem be (ts_add_set ep itsl) >= MS.mem be (ts_evict_set ep itsl)))

val lemma_add_seq_empty (ep: epoch) (itsl: its_log{I.length itsl = 0}):
  Lemma (ensures (S.length (ts_add_seq ep itsl) = 0))

val lemma_evict_seq_empty (ep: epoch) (itsl: its_log{I.length itsl = 0}):
  Lemma (ensures (S.length (ts_evict_seq ep itsl) = 0))

val lemma_add_seq_extend (itsl: its_log{I.length itsl > 0}):
  Lemma (requires (is_blum_add (I.telem itsl)))
        (ensures (let i = I.length itsl - 1 in
                  let itsl' = I.prefix itsl i in
                  let e = I.index itsl i in
                  let be = blum_add_elem e in
                  let ep = MH.epoch_of be in
                  ts_add_seq ep itsl ==
                  SA.append1 (ts_add_seq ep itsl') be))
                                       
val lemma_add_seq_extend2 (ep: epoch) (itsl: its_log{I.length itsl > 0}):
  Lemma (requires (not (is_blum_add (I.telem itsl))))
        (ensures (let i = I.length itsl - 1 in
                  let itsl' = I.prefix itsl i in
                  let e = I.index itsl i in
                  ts_add_seq ep itsl ==
                  ts_add_seq ep itsl'))

val lemma_evict_seq_extend (itsl: its_log{I.length itsl > 0}):
  Lemma (requires (is_evict_to_blum (I.telem itsl)))
        (ensures (let i = I.length itsl - 1 in
                  let itsl' = I.prefix itsl i in
                  let be = blum_evict_elem itsl i in
                  let ep = MH.epoch_of be in
                  ts_evict_seq ep itsl ==
                  SA.append1 (ts_evict_seq ep itsl') be))
                                       
val lemma_evict_seq_extend2 (ep: epoch) (itsl: its_log{I.length itsl > 0}):
  Lemma (requires (not (is_evict_to_blum (I.telem itsl))))
        (ensures (let i = I.length itsl - 1 in
                  let itsl' = I.prefix itsl i in
                  ts_evict_seq ep itsl ==
                  ts_evict_seq ep itsl'))
