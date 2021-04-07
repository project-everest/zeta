module Veritas.Verifier.TSLog

open Veritas.BinTree
open Veritas.EAC
open Veritas.Interleave
open Veritas.Key
open Veritas.MultiSetHash
open Veritas.Record
open Veritas.SeqAux
open Veritas.SeqMachine
open Veritas.State
open Veritas.Verifier
open Veritas.Verifier.Global
open Veritas.Verifier.Thread

open Veritas.SeqAux
open FStar.Seq
module SA = Veritas.SeqAux
module E=Veritas.EAC
module I = Veritas.Interleave
module V=Veritas.Verifier
module S = FStar.Seq
module VT = Veritas.Verifier.Thread
module VG = Veritas.Verifier.Global

(* an interleaving of vlog_entry *)
let il_vlog = interleaving vlog_entry

let thread_count (il:il_vlog) = length (I.s_seq il)

(* valid thread id given a number of threads *)
let valid_tid (il:il_vlog) = tid:nat{tid < thread_count il}

(* global vlogs that are the source of the interleaving *)
let g_vlog_of (il: il_vlog): g_vlog =
  I.s_seq il

(* an interleaving is verifiable if the source logs are verifiable *)
let verifiable (il: il_vlog) = 
  VG.verifiable (g_vlog_of il)

(* the clock of an entry in a verifiable idx seq *)
let clock (il: il_vlog{verifiable il}) (i: I.seq_index il): timestamp =
  let gl = g_vlog_of il in
  let j = i2s_map il i in
  VG.clock gl j

(*
let clock_sorted (il: il_vlog{verifiable il}) =
  forall (i:I.seq_index il). i > 0 ==> clock il (i - 1) `ts_leq` clock il i
*)
let clock_sorted (il: il_vlog{verifiable il}) =
 forall (i j:I.seq_index il). i <= j ==> clock il i `ts_leq` clock il j

(* TODO: add clock_sorted *)
let its_log = il:il_vlog{verifiable il /\ clock_sorted il}

let hash_verifiable (itsl: its_log) = VG.hash_verifiable (g_vlog_of itsl)

let hash_verifiable_log = 
  itsl:its_log {hash_verifiable itsl}

val lemma_prefix_verifiable (itsl: its_log) (i:nat{i <= I.length itsl}):
  Lemma (requires True)
        (ensures (verifiable (I.prefix itsl i) /\ clock_sorted (I.prefix itsl i)))
        [SMTPat (I.prefix itsl i)]

(* create a ts log *)
val create (gl: VG.verifiable_log): (itsl:its_log{g_vlog_of itsl == gl})

let state_ops (itsl: il_vlog): seq (state_op) =
  to_state_op_vlog (i_seq itsl)

let key_at (itsl: its_log) (i: I.seq_index itsl): key = 
  V.key_of (I.index itsl i)
  
let has_next_add_of_key (itsl: its_log) (i: I.seq_index itsl) (k:key): bool =
  has_next (is_add_of_key k) (I.i_seq itsl) i

let next_add_of_key
  (itsl: its_log) 
  (i:I.seq_index itsl) 
  (k:key{has_next_add_of_key itsl i k}): 
  (j:I.seq_index itsl{j > i && is_add_of_key k (I.index itsl j)}) = 
  next_index (is_add_of_key k) (I.i_seq itsl) i

let is_entry_of_key (k:key) (e:vlog_entry): bool = 
  key_of e = k

let has_some_entry_of_key (itsl: its_log) (k:key): bool = 
  exists_sat_elems (is_entry_of_key k) (I.i_seq itsl)

let last_idx_of_key (itsl: its_log) (k:key{has_some_entry_of_key itsl k}):
  I.seq_index itsl = 
  last_index (is_entry_of_key k) (I.i_seq itsl)

(* does the key k have some add *)
let has_some_add_of_key (itsl: its_log) (k:key): bool = 
  exists_sat_elems (is_add_of_key k) (I.i_seq itsl)

(* the last add index of a key *)
let last_add_idx (itsl: its_log) (k: key{has_some_add_of_key itsl k}): 
  (i:I.seq_index itsl{is_add_of_key k (I.index itsl i)}) = 
  last_index (is_add_of_key k) (I.i_seq itsl)

(* thread id of the ith entry *)
let thread_id_of (itsl: il_vlog) (i: I.seq_index itsl): valid_tid itsl =
  fst (i2s_map itsl i)

(* the verifier thread where the last add of key k happens *)
let last_add_tid (itsl: its_log) (k: key{has_some_add_of_key itsl k}): valid_tid itsl =
  thread_id_of itsl (last_add_idx itsl k)

(*thread state after processing ts log - guaranteed to be valid *)
val thread_state (itsl: il_vlog) (tid: valid_tid itsl): vtls

val lemma_thread_state_valid (itsl: its_log) (tid: valid_tid itsl)
  : Lemma (ensures (Valid? (thread_state itsl tid)))
          [SMTPat (thread_state itsl tid)]

val reveal_thread_state (itsl:il_vlog) (tid: valid_tid itsl)
  : Lemma (thread_state itsl tid == 
           verify (VG.thread_log (s_seq itsl) tid))

(* thread store after processing ts log *)
let thread_store (itsl: its_log) (tid: valid_tid itsl): vstore =
  Valid?.st (thread_state itsl tid)

let thread_state_pre (itsl: il_vlog) (i: I.seq_index itsl): vtls = 
  let tid = thread_id_of itsl i in
  thread_state (I.prefix itsl i) tid

let thread_state_post (itsl: il_vlog) (i: I.seq_index itsl): vtls = 
  let tid = thread_id_of itsl i in
  thread_state (I.prefix itsl (i + 1)) tid

(* 
 * let tid = thread_id_of itsl i. 
 * this lemma states that state of tid at (i+1) is obtained by the state at (i) 
 * applying the vlog entry at i.
 *)
val lemma_verifier_thread_state_extend (itsl: il_vlog) (i: I.seq_index itsl):
  Lemma (thread_state_post itsl i == 
         t_verify_step (thread_state_pre itsl i) (I.index itsl i))


let mk_vlog_entry_ext (itsl:its_log) (i:I.seq_index itsl)
  : vlog_entry_ext
  =   let ts = thread_state_pre itsl i in
      let Valid _ st clk _ _ _  = ts in
      let vle = Seq.index (i_seq itsl) i in
      lemma_verifier_thread_state_extend itsl i;
      match vle with
      | EvictM k k' ->
        let Some (VStore v _) = st k in
        EvictMerkle vle v
      | EvictB k ts ->
        let Some (VStore v _) = st k in
        EvictBlum vle v (thread_id_of itsl i)
      | EvictBM k k' ts ->
        let Some (VStore v _) = st k in
        EvictBlum vle v (thread_id_of itsl i)
      | v -> NEvict v

let vlog_ext_of_its_log (itsl:its_log)
  : seq vlog_entry_ext
  = SA.mapi (i_seq itsl) (mk_vlog_entry_ext itsl)

(* is this an evict add consistent log *)
val is_eac (itsl: its_log):bool

(* eac ts log *)
let eac_log = itsl: its_log {is_eac itsl}

(* non-eac ts log *)
type neac_log = itsl: its_log {not (is_eac itsl)}

val eac_boundary (itsl: neac_log):
  (i:I.seq_index itsl{is_eac (I.prefix itsl i) &&
                      not (is_eac (I.prefix itsl (i + 1)))})
                      
(* if itsl is eac, then any prefix is also eac *)
val lemma_eac_implies_prefix_eac (itsl: eac_log) (i:nat {i <= I.length itsl}):
  Lemma (requires True)
        (ensures (is_eac (I.prefix itsl i)))
        [SMTPat (I.prefix itsl i)]

(* if the ts log is eac, then its state ops are read-write consistent *)
val lemma_eac_implies_state_ops_rw_consistent (itsl: eac_log):
  Lemma (rw_consistent (state_ops itsl))
  
(* the eac state of a key at the end of an its log *)
val eac_state_of_key (itsl: its_log) (k:key): eac_state 

let eacs_t (itsl:its_log) = k:key -> e:eac_state { e == eac_state_of_key itsl k /\ (is_eac itsl ==> e <> EACFail) }
let threads_t (itsl:its_log) = t:valid_tid itsl -> v:vtls { Valid? v /\ v == verify (t, Seq.index (I.s_seq itsl) t) }

noeq
type monitored_state (itsl:its_log) = {
  eacs: eacs_t itsl;
  threads: threads_t itsl
}

val run_monitor (itsl:its_log)
  : monitored_state itsl

val run_monitor_empty (itsl:its_log{I.length itsl = 0}) (k:key)
  : Lemma
    (let m = run_monitor itsl in
     let vl = vlog_ext_of_its_log itsl in
     let vl' = partn eac_sm k vl in
     I.s_seq itsl == Seq.create (Seq.length (I.s_seq itsl)) empty /\
     m.eacs k == EACInit /\
     I.i_seq itsl == empty /\
     vl == empty /\
     vl' == empty /\
     (forall tid. thread_state itsl tid == init_thread_state tid)
     )

val run_monitor_step (itsl:its_log{I.length itsl > 0}) (k:key)
  : Lemma (let i = I.length itsl - 1 in
           let itsl' = I.prefix itsl i in
           let m' = run_monitor itsl' in
           let m = run_monitor itsl in
           let v = I.index itsl i in
           let ve = mk_vlog_entry_ext itsl i in
           let vl' = vlog_ext_of_its_log itsl' in
           let vl'_k = partn eac_sm k vl' in
           let vl = vlog_ext_of_its_log itsl in
           let vl_k = partn eac_sm k vl in
           let tid = thread_id_of itsl i in
           let _, tl' = thread_log (I.s_seq (I.prefix itsl i)) tid in
           let _, tl = thread_log (I.s_seq itsl) tid in
           vl `Seq.equal` Seq.snoc vl' ve /\
           tl `Seq.equal` Seq.snoc tl' v /\
           thread_state itsl tid == t_verify_step (thread_state itsl' tid) v /\
           (if key_of v <> k
            then (vl'_k == vl_k /\
                  m.eacs k == m'.eacs k)
            else (vl_k == Seq.snoc vl'_k ve /\
                  m.eacs k == eac_add ve (m'.eacs k))) /\
           (forall (tid':valid_tid itsl). {:pattern (thread_log (I.s_seq itsl) tid')}
             tid <> tid' ==>
             thread_log (I.s_seq itsl) tid' ==
             thread_log (I.s_seq (I.prefix itsl i)) tid'))

(* by definition, ts log is eac_valid only if the state of each key is not EACFail *)
val lemma_eac_state_of_key_valid (itsl: eac_log) (k:key):
  Lemma (EACFail <> eac_state_of_key itsl k)

(* is the eac state of key at the end of its_log init *)
let is_eac_state_init (itsl: its_log) (k:key): bool =
  eac_state_of_key itsl k = EACInit

(* is the key k in evicted state in *)
let is_eac_state_evicted (itsl: its_log) (k:key): bool = 
  EACEvictedMerkle? (eac_state_of_key itsl k) ||
  EACEvictedBlum? (eac_state_of_key itsl k) 

let eac_state_evicted_value (itsl: its_log) (k:key{is_eac_state_evicted itsl k}): value =
  let st = eac_state_of_key itsl k in
  match st with
  | EACEvictedMerkle v -> v
  | EACEvictedBlum v _ _ -> v

(* is the key currently evicted into merkle *)
let is_eac_state_evicted_merkle (itsl: its_log) (k:key): bool = 
  let st = eac_state_of_key itsl k in
  match st with
  | EACEvictedMerkle v -> true
  | _ -> false

(* is the key currently evicted into merkle *)
let is_eac_state_evicted_blum (itsl: its_log) (k:key): bool = 
  let st = eac_state_of_key itsl k in
  match st with
  | EACEvictedBlum v t j -> true
  | _ -> false

(* is the key k in instore state after processing its_log *)
let is_eac_state_instore (itsl: its_log) (k:key):bool = 
  EACInStore? (eac_state_of_key itsl k)

let is_eac_state_active (itsl: its_log) (k:key): bool = 
  is_eac_state_evicted itsl k ||
  is_eac_state_instore itsl k

(* the extended vlog entry to use for eac checking *)
val vlog_entry_ext_at (itsl: its_log) (i:I.seq_index itsl): 
  (e:vlog_entry_ext{E.to_vlog_entry e = I.index itsl i})

let eac_state_pre (itsl: its_log) (i:I.seq_index itsl): eac_state =
  let k = key_at itsl i in
  eac_state_of_key (I.prefix itsl i) k

let eac_boundary_state_pre (itsl: neac_log): (st:eac_state{EACFail <> st}) =
  let i = eac_boundary itsl in
  let k = key_at itsl i in
  lemma_eac_state_of_key_valid (I.prefix itsl i) k;
  eac_state_pre itsl (eac_boundary itsl)

let eac_state_post (itsl: its_log) (i:I.seq_index itsl): eac_state = 
  let k = key_at itsl i in
  eac_state_of_key (I.prefix itsl (i+1)) k

let eac_boundary_entry (itsl: neac_log): vlog_entry = 
  I.index itsl (eac_boundary itsl)

(* the eac state transition induced by the i'th entry *)
val lemma_eac_state_transition (itsl: its_log) (i:I.seq_index itsl):
  Lemma (eac_state_post itsl i = 
         eac_add (vlog_entry_ext_at itsl i) (eac_state_pre itsl i))

(* if the ith entry does not involve key k, the eac state of k is unchanged *)
val lemma_eac_state_same (itsl: its_log) (i: I.seq_index itsl) (k: key):
  Lemma (requires (key_at itsl i <> k))
        (ensures (eac_state_of_key (I.prefix itsl i) k == 
                  eac_state_of_key (I.prefix itsl (i + 1)) k))

val lemma_eac_boundary_state_transition (itsl: neac_log):
  Lemma (requires True)
        (ensures (eac_add (vlog_entry_ext_at itsl (eac_boundary itsl))
                          (eac_boundary_state_pre itsl) = EACFail))
        [SMTPat (eac_boundary itsl)]

let lemma_verifier_boundary_thread_state (itsl: neac_log):
  Lemma (requires True)
        (ensures (thread_state_post itsl (eac_boundary itsl) == 
                  t_verify_step (thread_state_pre itsl (eac_boundary itsl)) 
                                (I.index itsl (eac_boundary itsl))))
        [SMTPat (eac_boundary itsl)] =
  lemma_verifier_thread_state_extend itsl (eac_boundary itsl)


val lemma_thread_id_of_prefix (il:il_vlog) (j:nat{ j <= I.length il}) (i:I.seq_index il { i < j })
  : Lemma (thread_id_of il i == thread_id_of (I.prefix il j) i)

val lemma_thread_state_pre_prefix (il:il_vlog) (j:nat{ j <= I.length il}) (i:I.seq_index il { i < j })
  : Lemma (thread_state_pre il i == thread_state_pre (I.prefix il j) i)

val lemma_thread_state_post_prefix (il:il_vlog) (j:nat{ j <= I.length il}) (i:I.seq_index il { i < j })
  : Lemma (thread_state_post il i == thread_state_post (I.prefix il j) i)

(* If the i'th entry does not go to thread tid, then its state remains unchanged when processing 
 * the i'th entry *)
val lemma_verifier_thread_state_frame (il: il_vlog { I.length il > 0 })
                                      (tid: valid_tid il)
  : Lemma (requires (tid <> thread_id_of il (I.length il - 1)))
          (ensures (thread_state il tid == thread_state (I.hprefix il) tid))
 
val lemma_verifier_thread_state_extend2 (itsl: il_vlog) (i: I.seq_index itsl) (tid: valid_tid itsl):
  Lemma (requires (tid <> thread_id_of itsl i))
        (ensures (thread_state (I.prefix itsl (i + 1)) tid == 
                  thread_state (I.prefix itsl i) tid))

(* when the eac state of a key is "instore" then there is always a previous add *)
val lemma_eac_state_active_implies_prev_add (itsl: eac_log) 
  (k:key{is_eac_state_active itsl k}):
  Lemma (requires True)
        (ensures (has_some_add_of_key itsl k))
        [SMTPat (is_eac_state_instore itsl k)]

(* the converse of the previous, eac state init implies no previous add *)
val lemma_eac_state_init_no_entry (itsl: eac_log) (k:key):
  Lemma (requires (is_eac_state_init itsl k))
        (ensures (not (has_some_entry_of_key itsl k)))

(* add method of an eac state *)
val lemma_eac_state_addm (itsl: eac_log) (k:key{is_eac_state_instore itsl k}):
  Lemma (E.add_method_of (eac_state_of_key itsl k) = 
         V.addm_of_entry (I.index itsl (last_add_idx itsl k)))

(* the evicted value is always of the correct type for the associated key *)
val lemma_eac_value_correct_type (itsl: eac_log) (k:key):  
  Lemma (requires (E.is_eac_state_active (eac_state_of_key itsl k)))
        (ensures is_value_of k (E.value_of (eac_state_of_key itsl k)))

(* value associated with eac state *)
let eac_state_value (itsl: eac_log) (k:key{is_eac_state_active itsl k}): value_type_of k = 
  let st = eac_state_of_key itsl k in
  lemma_eac_value_correct_type itsl k;
  E.value_of st

(* we never see operations on Root so its eac state is always init *)
val lemma_eac_state_of_root_init (itsl: eac_log):
  Lemma (is_eac_state_init itsl Root)

(* 
 * when the eac state of a key is Init (no operations on the key yet) no 
 * thread contains the key in its store. Valid only for non-root keys 
 * since we start off with the root in the cache of thread 0
 *)
val lemma_eac_state_init_store (itsl: eac_log) (k: key) (tid:valid_tid itsl):
  Lemma (requires (k <> Root && is_eac_state_init itsl k))
        (ensures (not (store_contains (thread_store itsl tid) k)))

(* when the eac state of a key is evicted then no thread contains the key in its store *)
val lemma_eac_state_evicted_store  (itsl: eac_log) (k: key{is_eac_state_evicted itsl k}) 
  (tid:valid_tid itsl):
  Lemma (not (store_contains (thread_store itsl tid) k))


val lemma_key_in_unique_store2 (itsl: eac_log) (k:key) (tid1 tid2: valid_tid itsl):
  Lemma (requires (tid1 <> tid2))
        (ensures (not (store_contains (thread_store itsl tid1) k &&
                       store_contains (thread_store itsl tid2) k)))

(* when the eac_state of k is instore, then k is in the store of a unique verifier thread *)
val stored_tid (itsl: eac_log) (k:key{is_eac_state_instore itsl k}): 
  (tid: valid_tid itsl{store_contains (thread_store itsl tid) k})

(* uniqueness: k is not in any store other than stored_tid *)
val lemma_key_in_unique_store (itsl: eac_log) (k:key) (tid: valid_tid itsl):
  Lemma (requires (is_eac_state_instore itsl k))
        (ensures (tid <> stored_tid itsl k ==> not (store_contains (thread_store itsl tid) k)))


(* it is therefore meaningful to talk of the stored value of a key *)
let stored_value (itsl: eac_log) (k:key{is_eac_state_instore itsl k}): value_type_of k =
  V.stored_value (thread_store itsl (stored_tid itsl k)) k

let stored_add_method (itsl: eac_log) (k:key {is_eac_state_instore itsl k}): add_method =
  V.add_method_of (thread_store itsl (stored_tid itsl k)) k

(* for data keys, the value in the store is the same as the value associated with the eac state *)
val lemma_eac_stored_value (itsl: eac_log) (k: data_key{is_eac_state_instore itsl k}):
  Lemma (eac_state_value itsl k = stored_value itsl k)

(* 
 * for all keys, the add method stored in the store is the same as the add method associated 
 * with eac state
 *)
val lemma_eac_stored_addm (itsl: eac_log) (k:key{is_eac_state_instore itsl k}):
  Lemma (E.add_method_of (eac_state_of_key itsl k) = stored_add_method itsl k)
  
(* if k is in a verifier store, then its eac_state is instore *)
val lemma_instore_implies_eac_state_instore (itsl:eac_log) (k:key{k <> Root}) (tid:valid_tid itsl):
  Lemma (store_contains (thread_store itsl tid) k ==> is_eac_state_instore itsl k)
         
(* the root is always in thread 0 *)
val lemma_root_in_store0 (itsl: eac_log{thread_count itsl > 0}):
  Lemma (store_contains (thread_store itsl 0) Root)

val lemma_root_not_in_store (itsl: eac_log) (tid:valid_tid itsl{tid > 0}):
  Lemma (not (store_contains (thread_store itsl tid) Root))

(* we use eac constraints to associate a value with each key *)
val eac_value (itsl: eac_log) (k:key): value_type_of k

(* eac_value is consistent with stored value *)
val lemma_eac_value_is_stored_value (itsl: eac_log) (k:key) (tid: valid_tid itsl):  
  Lemma (requires (store_contains (thread_store itsl tid) k))
        (ensures (eac_value itsl k = V.stored_value (thread_store itsl tid) k))

val lemma_eac_value_is_evicted_value (itsl: eac_log) (k:key):
  Lemma (requires (is_eac_state_evicted itsl k))
        (ensures (eac_state_evicted_value itsl k = eac_value itsl k))

val lemma_ext_evict_val_is_stored_val (itsl: its_log) (i: I.seq_index itsl):
  Lemma (requires (is_evict (I.index itsl i)))
        (ensures (store_contains (thread_store (I.prefix itsl i) (thread_id_of itsl i)) (key_at itsl i) /\
                  is_evict_ext (vlog_entry_ext_at itsl i) /\
                  V.stored_value (thread_store (I.prefix itsl i) (thread_id_of itsl i)) (key_at itsl i) = 
                  value_ext (vlog_entry_ext_at itsl i)))

(* if an evict is not the last entry of a key, then there is a add subsequent to the 
 * evict *)
val lemma_evict_has_next_add (itsl: its_log) 
                             (i:I.seq_index itsl)
                             (j:nat { i < j /\ j <= I.length itsl }):
  Lemma (requires (is_evict (I.index itsl i) /\
                   is_eac (I.prefix itsl j) /\         
                   exists_sat_elems (is_entry_of_key (key_of (I.index itsl i))) (I.i_seq itsl)) /\
                   i < last_idx_of_key itsl (key_of (I.index itsl i)))
        (ensures (has_next_add_of_key itsl i (key_of (I.index itsl i))))

val lemma_root_never_evicted (itsl: its_log) (i:I.seq_index itsl):
  Lemma (requires (is_evict (I.index itsl i)))
        (ensures (V.key_of (I.index itsl i) <> Root))

(* since the itsl is sorted by clock, the following lemma holds *)
val lemma_clock_ordering (itsl: its_log) (i1 i2: I.seq_index itsl):
  Lemma (requires (clock itsl i1 `ts_lt` clock itsl i2))
        (ensures (i1 < i2))
  
(* the state of each key for an empty log is init *)
val lemma_init_state_empty (itsl: its_log {I.length itsl = 0}) (k: key):
  Lemma (eac_state_of_key itsl k = EACInit)

val lemma_eac_value_init (itsl: eac_log) (k:key{k <> Root}):
  Lemma (requires (is_eac_state_init itsl k))
        (ensures (eac_value itsl k = init_value k))

(* TODO: oddly enough, this fails if we hardcode k = Root in the statement of the lemma *)
val lemma_eac_value_root_init (itsl: eac_log {I.length itsl = 0}) (k:key{k = Root}):
  Lemma (eac_value itsl k = init_value k)

val lemma_addm_ancestor_merkle (itsl: its_log) (i: I.seq_index itsl{is_merkle_add (I.index itsl i)}):
  Lemma (ensures (let AddM _ k' = I.index itsl i in
                  is_merkle_key k'))
                      
val lemma_evictm_ancestor_merkle (itsl: its_log) (i:I.seq_index itsl{is_evict_to_merkle (I.index itsl i)}):
  Lemma (ensures (let EvictM _ k' = I.index itsl i in
                  is_merkle_key k'))

val lemma_evictbm_ancestor_merkle (itsl: its_log) (i:I.seq_index itsl{EvictBM? (I.index itsl i)}):
  Lemma (ensures (let EvictBM _ k' _ = I.index itsl i in
                  is_merkle_key k'))

val lemma_eac_boundary_inv (itsl: its_log) (i:I.seq_index itsl): 
  Lemma (requires (is_eac (I.prefix itsl i) /\
                   not (is_eac (I.prefix itsl (i + 1)))))
        (ensures (eac_boundary itsl = i)) 

///  If a key is in store, then the last entry of the key cannot be an evict
/// 
val lemma_instore_implies_last_entry_non_evict (itsl: eac_log) (k:key) (tid:valid_tid itsl):
  Lemma (requires (store_contains (thread_store itsl tid) k))
        (ensures (has_some_entry_of_key itsl k ==> 
                  not (is_evict_to_blum (I.index itsl (last_idx_of_key itsl k))))) 

/// An empty log is eac
/// 
val lemma_empty_log_eac (itsl: its_log{I.length itsl = 0})
  : Lemma (ensures (is_eac itsl))

let blum_evict_elem (itsl: its_log) 
                    (i:I.seq_index itsl{is_evict_to_blum (I.index itsl i)}): ms_hashfn_dom = 
  let gl = g_vlog_of itsl in
  let ii = i2s_map itsl i in
  VG.blum_evict_elem gl ii

val lemma_blum_evict_def (itsl: its_log)
                         (i:I.seq_index itsl{is_evict_to_blum (I.index itsl i)}):
  Lemma (ensures (let tid = thread_id_of itsl i in 
                  let e = I.index itsl i in
                  let k = key_of e in
                  let itsli = I.prefix itsl i in
                  let st = thread_store itsli tid in
                  V.store_contains st k /\
                  (let v = V.stored_value st k in
                   match e with
                   | EvictB _ t -> blum_evict_elem itsl i = MHDom (k,v) t tid
                   | EvictBM _ _ t -> blum_evict_elem itsl i = MHDom (k,v) t tid)))
