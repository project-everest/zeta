module Veritas.Verifier.Blum

open Veritas.EAC

module S = FStar.Seq
module SA = Veritas.SeqAux
module E = Veritas.EAC
module VT = Veritas.Verifier.Thread

let rec ts_add_seq_aux (itsl: its_log): 
  Tot (seq ms_hashfn_dom) 
  (decreases (I.length itsl)) = 
  let n = I.length itsl in
  if n = 0 then S.empty #ms_hashfn_dom
  else
    let itsl' = I.prefix itsl (n - 1) in
    let s' = ts_add_seq_aux itsl' in
    let e = I.index itsl (n - 1) in
    if is_blum_add e then 
      SA.append1 s' (blum_add_elem e)
    else
      s'
  
let ts_add_seq = ts_add_seq_aux

(* map an index of ts containing a blum add to its position in 
 * the ts_add_seq *)
let rec add_seq_map 
  (itsl: its_log) 
  (i: I.seq_index itsl{is_blum_add (I.index itsl i)}): 
  Tot (j:SA.seq_index (ts_add_seq itsl){S.index (ts_add_seq itsl) j = 
                                        blum_add_elem (I.index itsl i)})
  (decreases (I.length itsl)) =                                         
  let n = I.length itsl in
  let s = ts_add_seq itsl in
  if n = 0 then 0    
  else 
    let itsl' = I.prefix itsl (n - 1) in
    let s' = ts_add_seq itsl' in
    if i = n - 1 then S.length s'
    else add_seq_map itsl' i

let lemma_add_elem_correct (itsl: its_log) (i: I.seq_index itsl):
  Lemma (requires (is_blum_add (I.index itsl i)))
        (ensures (contains (blum_add_elem (I.index itsl i)) (ts_add_set itsl))) = 
  let sa = ts_add_seq itsl in        
  let j = add_seq_map itsl i in
  //assert(S.index sa j = blum_add_elem (I.index itsl i));
  lemma_seq_elem sa j

let rec ts_add_seq_key_aux (itsl: its_log) (k:key): 
  Tot (seq ms_hashfn_dom) 
  (decreases (I.length itsl)) = 
  let n = I.length itsl in
  if n = 0 then S.empty #ms_hashfn_dom
  else
    let itsl' = I.prefix itsl (n - 1) in
    let s' = ts_add_seq_key_aux itsl' k in
    let e = I.index itsl (n - 1) in
    if is_blum_add e && key_of e = k  then 
      SA.append1 s' (blum_add_elem e)
    else
      s'

let ts_add_seq_key (itsl: its_log) (k:key): seq ms_hashfn_dom =
  ts_add_seq_key_aux itsl k

let lemma_ts_add_set_correct (itsl: its_log): 
  Lemma (ts_add_set itsl == g_add_set (g_vlog_of itsl)) = admit()

let lemma_ts_add_set_key_extend (itsl: its_log {I.length itsl > 0}):
  Lemma (requires (is_blum_add (I.telem itsl)))
        (ensures (ts_add_set_key itsl (key_of (I.index itsl (I.length itsl - 1))) == 
                  add_elem (ts_add_set_key (I.prefix itsl (I.length itsl - 1))
                                           (key_of (I.index itsl (I.length itsl - 1))))
                           (blum_add_elem (I.telem itsl)))) =
  admit()

let lemma_ts_add_set_key_contains_only (itsl: its_log) (k:key) (be: ms_hashfn_dom):
  Lemma (requires (MS.contains be (ts_add_set_key itsl k)))
        (ensures (MH.key_of be = k)) = admit()

let some_add_elem_idx (itsl: its_log) 
  (be: ms_hashfn_dom{MS.contains be (ts_add_set itsl)}): 
  (i:(I.seq_index itsl){is_blum_add (I.index itsl i) /\
                      be = blum_add_elem (I.index itsl i)}) = admit()

(* get the blum evict element from an index *)
let blum_evict_elem (itsl: its_log) (i:I.seq_index itsl{is_evict_to_blum (I.index itsl i)}):
  (e:ms_hashfn_dom{MH.key_of e = key_of (I.index itsl i)}) = admit()

let lemma_index_blum_evict_prefix (itsl: its_log) (i:nat{i <= I.length itsl}) (j:nat{j < i}):
  Lemma (requires (is_evict_to_blum (I.index itsl j)))
        (ensures (blum_evict_elem itsl j = blum_evict_elem (I.prefix itsl i) j))
        [SMTPat (blum_evict_elem (I.prefix itsl i) j)] = admit()


(* sequence of evicts in time sequence log *)
let ts_evict_seq (itsl: its_log): seq ms_hashfn_dom = admit()

(* the evict sequence restricted to key k *)
let ts_evict_seq_key (itsl: its_log) (k:key): seq ms_hashfn_dom = admit()

(* the blum evicts in time sequenced log should be the same as global evict set *)
let lemma_ts_evict_set_correct (itsl: its_log):
  Lemma (ts_evict_set itsl == g_evict_set (g_vlog_of itsl)) = admit()

(* if the tail element is not an evict, the evict set is the same as the evict 
 * set of the length - 1 prefix 
 *)
let lemma_ts_evict_set_key_extend2 (itsl: its_log {I.length itsl > 0}):
  Lemma (requires (not (is_evict_to_blum (I.index itsl (I.length itsl - 1)))))
        (ensures (ts_evict_set_key itsl (key_of (I.index itsl (I.length itsl - 1))) == 
                  ts_evict_set_key (I.prefix itsl (I.length itsl - 1))
                                           (key_of (I.index itsl (I.length itsl - 1))))) = admit()

(* since evict_set is a pure set (not a multiset) we can identify the unique index 
 * for each element of the set *)
let index_blum_evict (itsl: its_log) (e: ms_hashfn_dom {contains e (ts_evict_set itsl)}):
  (i:I.seq_index itsl{is_evict_to_blum (I.index itsl i) /\ 
                    blum_evict_elem itsl i = e}) = admit()

(* if the blum add occurs in the blum evict set, its index is earlier *)
let lemma_evict_before_add (itsl: its_log) (i:I.seq_index itsl{is_blum_add (I.index itsl i)}):
  Lemma (requires True)
        (ensures (not (contains (blum_add_elem (I.index itsl i)) (ts_evict_set itsl)) \/
                  index_blum_evict itsl (blum_add_elem (I.index itsl i)) < i)) = admit()

(* a slightly different version of of the previous lemma - the count of an add element 
 * in the evict set is the same in the prefix as the full sequence *)
let lemma_evict_before_add2 (itsl: its_log) (i:I.seq_index itsl{is_blum_add (I.index itsl i)}):
   Lemma (requires True)
         (ensures (MS.mem (blum_add_elem (I.index itsl i)) (ts_evict_set itsl) =
                   MS.mem (blum_add_elem (I.index itsl i)) (ts_evict_set (I.prefix itsl i)))) = admit()

let lemma_evict_before_add3 (itsl: its_log) (i: I.seq_index itsl) (j:I.seq_index itsl):
  Lemma (requires (is_blum_add (I.index itsl i) /\
                   is_evict_to_blum (I.index itsl j) /\
                   blum_add_elem (I.index itsl i) = blum_evict_elem itsl j))
        (ensures (j < i)) = admit()

(* for an eac ts log, if the eac state of a key k is instore, the count of blum evicts 
 * is the same of blum adds for that key *)
let lemma_evict_add_count_same (itsl: TL.eac_log) (k:key):
  Lemma (requires (TL.is_eac_state_instore itsl k))
        (ensures (MS.size (ts_add_set_key itsl k) = MS.size (ts_evict_set_key itsl k))) = admit()

(* for an eac ts log, if the eac state of a key k is evicted to merkle, the count of blum evicts 
 * is the same of blum adds for that key *)
let lemma_evict_add_count_same_evictedm (itsl: TL.eac_log) (k:key):
  Lemma (requires (is_eac_state_evicted_merkle itsl k))
        (ensures (MS.size (ts_add_set_key itsl k) = MS.size (ts_evict_set_key itsl k))) = admit()

let lemma_mem_key_add_set_same (itsl: its_log) (be: ms_hashfn_dom):
  Lemma (mem be (ts_add_set itsl) = mem be (ts_add_set_key itsl (MH.key_of be))) = admit()

let lemma_mem_key_evict_set_same (itsl: its_log) (be: ms_hashfn_dom):
  Lemma (mem be (ts_evict_set itsl) = mem be (ts_evict_set_key itsl (MH.key_of be))) =admit()

(* the count of an element can only decrease in a prefix of itsl *)
let lemma_mem_monotonic (be:ms_hashfn_dom) (itsl: its_log) (i:nat{i <= I.length itsl}):
  Lemma (mem be (ts_evict_set itsl) >= mem be (ts_evict_set (I.prefix itsl i)) /\
         mem be (ts_add_set itsl) >= mem be (ts_add_set (I.prefix itsl i))) = admit()

(* the next add of a blum evict is a blum add of the same "element" *)
let lemma_blum_evict_add_same (itsl: TL.eac_log) (i:I.seq_index itsl):
  Lemma (requires (is_evict_to_blum (I.index itsl i) /\
                   TL.has_next_add_of_key itsl i (key_of (I.index itsl i))))
        (ensures (is_blum_add (I.index itsl (TL.next_add_of_key itsl i (key_of (I.index itsl i)))) /\
                  blum_evict_elem itsl i =                                   
                  blum_add_elem (I.index itsl (TL.next_add_of_key itsl i (key_of (I.index itsl i)))))) = admit()

(* when the eac store is evicted, there exists a previous evict *)
let lemma_eac_evicted_blum_implies_previous_evict (itsl: its_log) (k:key):
  Lemma (requires (is_eac_state_evicted_blum itsl k))
        (ensures (has_some_entry_of_key itsl k /\
                  is_evict_to_blum (I.index itsl (last_idx_of_key itsl k)) /\
                  blum_evict_elem itsl (last_idx_of_key itsl k) = 
                  to_blum_elem (eac_state_of_key itsl k) k)) = admit()

(* if we provide two indexes having the same add element then the membership of the element in the 
 * add set is at least two *)
let lemma_add_set_mem (itsl: its_log) (i: I.seq_index itsl) (j:I.seq_index itsl{j <> i}):
  Lemma (requires (is_blum_add (I.index itsl i) /\
                   is_blum_add (I.index itsl j) /\
                   blum_add_elem (I.index itsl i) = blum_add_elem (I.index itsl j)))
        (ensures (MS.mem (blum_add_elem (I.index itsl i)) (ts_add_set itsl) >= 2)) = admit()
