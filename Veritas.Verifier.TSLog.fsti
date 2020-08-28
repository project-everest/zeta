module Veritas.Verifier.TSLog

open Veritas.BinTree
open Veritas.EAC
open Veritas.Interleave
open Veritas.Key
open Veritas.MultiSetHash
open Veritas.Record
open Veritas.SeqAux
open Veritas.SeqMachine
open Veritas.Verifier
open Veritas.Verifier.Global
open Veritas.Verifier.Thread

open Veritas.SeqAux
open FStar.Seq

module E=Veritas.EAC
module V=Veritas.Verifier
module S = FStar.Seq
module VT = Veritas.Verifier.Thread
module VG = Veritas.Verifier.Global

(* valid thread id given a number of threads *)
let valid_tid (p:pos) = tid:nat{tid < p}

(* vlog entry and tid that it went to *)
let vlog_entry_tid (p:pos) = idx_elem #vlog_entry p

(* cast to vlog entry *)
let to_vlog_entry (#p:pos) (e: vlog_entry_tid p): vlog_entry = 
  fst e

(* 
 * an indexed sequence log represents and interleaving of a global log (a sequence of thread-level
 * verifier logs. It is a sequence of the form (e,tid) where e denotes a verifier log entry
 * and tid denotes the verifier thread that the entry comes from
 *)
let idx_seq_vlog (p:pos) = seq (vlog_entry_tid p)

(* 
 * an idx_seq_vlog is verifiable if the global sequence of logs that results from partitioning 
 * by the second element (tid) of a pair is verifiable 
 *)
let verifiable (#p:pos) (s: idx_seq_vlog p) = 
  VG.verifiable (partition_idx_seq s)

(* the clock of an entry in a verifiable idx seq *)
val clock (#p:pos) (s: idx_seq_vlog p{verifiable s}) (i: seq_index s): timestamp

let clock_sorted (#p:pos) (s: idx_seq_vlog p{verifiable s}) =
  forall (i:seq_index s). i > 0 ==> clock s (i - 1) `ts_leq` clock s i

let its_log (p:pos) = 
  s:idx_seq_vlog p{verifiable s}

let hash_verifiable_log (p:pos) = 
  itsl:its_log p {VG.hash_verifiable (partition_idx_seq itsl)}

val lemma_prefix_verifiable (#p:pos) (itsl: its_log p) (i:nat{i <= length itsl}):
  Lemma (requires True)
        (ensures (verifiable (prefix itsl i)))
        [SMTPat (prefix itsl i)]

(* create a ts log *)
val create (gl: VG.verifiable_log): its_log (length gl)

(* get back the verifier logs from ts log *)
let to_g_vlog (#p:pos) (itsl: its_log p): VG.verifiable_log =
  partition_idx_seq itsl

(* we get back the global logs used to crate ts log with t_g_vlog *)
val lemma_create_correct (gl: VG.verifiable_log):
  Lemma (gl = to_g_vlog (create gl))

(* the log entry referenced by the ith entry *)
let vlog_entry_at (#p:pos) (itsl: its_log p) (i: seq_index itsl): vlog_entry =
  fst (index itsl i)

(* the key referenced by the i'th entry *)
let key_of (#p:pos) (e: vlog_entry_tid p): key =
  V.key_of (to_vlog_entry e)

let key_at (#p:pos) (itsl: its_log p) (i: seq_index itsl): key = 
  V.key_of (vlog_entry_at itsl i)

let is_add (#p:pos) (e: vlog_entry_tid p): bool = 
  V.is_add (fst e)

let is_add_of_key (#p:pos) (k:key) (e: vlog_entry_tid p): bool = 
  is_add e && 
  key_of e = k

(* is the i'th index of itsl a blum add *)
let is_blum_add (#p:pos) (ie:vlog_entry_tid p):bool =
  let (e,_) = ie in
  match e with
  | AddB _ _ _ -> true
  | _ -> false

let is_evict (#p:pos) (e:vlog_entry_tid p): bool = 
  V.is_evict (to_vlog_entry e)

(* is the index i of ts log an blum evict *)
let is_blum_evict (#p:pos) (ie:vlog_entry_tid p): bool = 
  let (e,_) = ie in
  match e with
  | EvictB _ _ -> true
  | EvictBM _ _ _ -> true
  | _ -> false

let is_evict_of_key (k:key) (#p:pos) (ie:vlog_entry_tid p): bool = 
  is_evict ie &&
  key_of ie = k
  
let has_next_add_of_key (#p:pos) (itsl: its_log p) (i:seq_index itsl) (k:key): bool =
  has_next (is_add_of_key k) itsl i

let next_add_of_key (#p:pos) 
  (itsl: its_log p) 
  (i:seq_index itsl) (k:key{has_next_add_of_key itsl i k}): 
  (j:seq_index itsl{j > i && is_add_of_key k (index itsl j)}) = 
  next_index (is_add_of_key k) itsl i

let is_entry_of_key (k:key) (#p:pos) (e:vlog_entry_tid p): bool = 
  key_of e = k

let has_some_entry_of_key (#p:pos) (itsl: its_log p) (k:key): bool = 
  exists_sat_elems (is_entry_of_key k) itsl

let last_idx_of_key (#p:pos) (itsl: its_log p) (k:key{has_some_entry_of_key itsl k}):
  seq_index itsl = 
  last_index (is_entry_of_key k) itsl

let add_method_of (#p:pos) (e:vlog_entry_tid p{is_add e}): add_method = 
  V.addm_of_entry (to_vlog_entry e)

(* does the key k have some add *)
let has_some_add_of_key (#p:pos) (itsl: its_log p) (k:key): bool = 
  exists_sat_elems (is_add_of_key k) itsl

(* when the eac state of a key is instore return the index of the last add that transitioned
 * the key k to "instore" *)
val last_add_idx (#p:pos) (itsl: its_log p) (k: key{has_some_add_of_key itsl k}): 
  (i:seq_index itsl{is_add_of_key k (index itsl i)})

(* thread id of the ith entry *)
let thread_id_of (#p:pos) (itsl: its_log p) (i: seq_index itsl): valid_tid p =
  snd (index itsl i)  

(* the verifier thread where the last add of key k happens *)
let last_add_tid (#p:pos) (itsl: its_log p) (k: key{has_some_add_of_key itsl k}): valid_tid p =
  thread_id_of itsl (last_add_idx itsl k)

(*thread state after processing ts log - guaranteed to be valid *)
val thread_state (#p:pos) (itsl: its_log p) (tid: valid_tid p): (vs:vtls{Valid? vs})

(* thread store after processing ts log *)
let thread_store (#p:pos) (itsl: its_log p) (tid: valid_tid p): vstore =
  Valid?.st (thread_state itsl tid)

(* 
 * let tid = thread_id_of itsl i. 
 * this lemma states that state of tid at (i+1) is obtained by the state at (i) 
 * applying the vlog entry at i.
 *)
val lemma_verifier_thread_state_extend (#p:pos) (itsl: its_log p) (i:seq_index itsl):
  Lemma (thread_state (prefix itsl (i + 1)) (thread_id_of itsl i)== 
         t_verify_step (thread_state (prefix itsl i) (thread_id_of itsl i))
                       (vlog_entry_at itsl i))

(* is this an evict add consistent log *)
val is_eac (#p:pos) (itsl: its_log p):bool

(* eac ts log *)
let eac_log (p:pos) = itsl: its_log p {is_eac itsl}

(* non-eac ts log *)
type neac_log (p:pos) = itsl: its_log p {not (is_eac itsl)}

(* if itsl is eac, then any prefix is also eac *)
val lemma_eac_implies_prefix_eac (#p:pos) (itsl: eac_log p) (i:nat {i <= length itsl}):
  Lemma (requires True)
        (ensures (is_eac (prefix itsl i)))
        [SMTPat (prefix itsl i)]

(* the eac state of a key at the end of an its log *)
val eac_state_of_key (#p:pos) (itsl: its_log p) (k:key): eac_state 

(* by definition, ts log is eac_valid only if the state of each key is not EACFail *)
val lemma_eac_state_of_key_valid (#p:pos) (itsl: eac_log p) (k:key):
  Lemma (EACFail <> eac_state_of_key itsl k)

(* is the eac state of key at the end of its_log init *)
let is_eac_state_init (#p:pos) (itsl: its_log p) (k:key): bool =
  eac_state_of_key itsl k = EACInit

(* is the key k in evicted state in *)
let is_eac_state_evicted (#p:pos) (itsl: its_log p) (k:key): bool = 
  EACEvictedMerkle? (eac_state_of_key itsl k) ||
  EACEvictedBlum? (eac_state_of_key itsl k) 

let eac_state_evicted_value (#p:pos) (itsl: its_log p) (k:key{is_eac_state_evicted itsl k}): value =
  let st = eac_state_of_key itsl k in
  match st with
  | EACEvictedMerkle v -> v
  | EACEvictedBlum v _ _ -> v

(* is the key currently evicted into merkle *)
let is_eac_state_evicted_merkle (#p:pos) (itsl: its_log p) (k:key): bool = 
  let st = eac_state_of_key itsl k in
  match st with
  | EACEvictedMerkle v -> true
  | _ -> false

(* is the key currently evicted into merkle *)
let is_eac_state_evicted_blum (#p:pos) (itsl: its_log p) (k:key): bool = 
  let st = eac_state_of_key itsl k in
  match st with
  | EACEvictedBlum v t j -> true
  | _ -> false

(* is the key k in instore state after processing its_log *)
let is_eac_state_instore (#p:pos) (itsl: its_log p) (k:key):bool = 
  EACInStore? (eac_state_of_key itsl k)

let is_eac_state_active (#p:pos) (itsl: its_log p) (k:key): bool = 
  is_eac_state_evicted itsl k ||
  is_eac_state_instore itsl k

(* the extended vlog entry to use for eac checking *)
val vlog_entry_ext_at (#p:pos) (itsl: its_log p) (i:seq_index itsl): 
  (e:vlog_entry_ext{E.to_vlog_entry e = vlog_entry_at itsl i})

(* the eac state transition induced by the i'th entry *)
val lemma_eac_state_transition (#p:pos) (itsl: its_log p) (i:seq_index itsl):
  Lemma (eac_state_of_key (prefix itsl (i + 1)) (key_at itsl i) = 
         eac_add (vlog_entry_ext_at itsl i) 
                 (eac_state_of_key (prefix itsl i) (key_at itsl i)))

(* when the eac state of a key is "instore" then there is always a previous add *)
val lemma_eac_state_active_implies_prev_add (#p:pos) (itsl: eac_log p) 
  (k:key{is_eac_state_active itsl k}):
  Lemma (requires True)
        (ensures (has_some_add_of_key itsl k))
        [SMTPat (is_eac_state_instore itsl k)]

(* add method of an eac state *)
val lemma_eac_state_addm (#p:pos) (itsl: eac_log p) (k:key{is_eac_state_instore itsl k}):
  Lemma (E.add_method_of (eac_state_of_key itsl k) = 
         add_method_of (index itsl (last_add_idx itsl k)))

(* the evicted value is always of the correct type for the associated key *)
val lemma_eac_value_correct_type (#p:pos) (itsl: eac_log p) (k:key):  
  Lemma (requires (E.is_eac_state_active (eac_state_of_key itsl k)))
        (ensures is_value_of k (E.value_of (eac_state_of_key itsl k)))

(* value associated with eac state *)
val eac_state_value (#n:pos) (itsl: eac_log n) (k:key{is_eac_state_active itsl k}): value_type_of k

(* we never see operations on Root so its eac state is always init *)
val lemma_eac_state_of_root_init (#p:pos) (itsl: eac_log p):
  Lemma (is_eac_state_init itsl Root)

(* 
 * when the eac state of a key is Init (no operations on the key yet) no 
 * thread contains the key in its store. Valid only for non-root keys 
 * since we start off with the root in the cache of thread 0
 *)
val lemma_eac_state_init_store (#p:pos) (itsl: eac_log p) (k: key) (tid:valid_tid p):
  Lemma (requires (k <> Root && is_eac_state_init itsl k))
        (ensures (not (store_contains (thread_store itsl tid) k)))

(* when the eac state of a key is evicted then no thread contains the key in its store *)
val lemma_eac_state_evicted_store  (#p:pos) (itsl: eac_log p) (k: key{is_eac_state_evicted itsl k}) 
  (tid:valid_tid p):
  Lemma (not (store_contains (thread_store itsl tid) k))

(* when the eac_state of k is instore, then k is in the store of a unique verifier thread *)
val stored_tid (#p:pos) (itsl: eac_log p) (k:key{is_eac_state_instore itsl k}): 
  (tid: valid_tid p{store_contains (thread_store itsl tid) k})

(* uniqueness: k is not in any store other than stored_tid *)
val lemma_key_in_unique_store (#p:pos) (itsl: eac_log p) (k:key) (tid: valid_tid p):
  Lemma (requires (is_eac_state_instore itsl k /\ tid <> stored_tid itsl k))
        (ensures (not (store_contains (thread_store itsl tid) k)))

(* it is therefore meaningful to talk of the stored value of a key *)
let stored_value (#p:pos) (itsl: eac_log p) (k:key{is_eac_state_instore itsl k}): value_type_of k =
  V.stored_value (thread_store itsl (stored_tid itsl k)) k

let stored_add_method (#p:pos) (itsl: eac_log p) (k:key {is_eac_state_instore itsl k}): add_method =
  V.add_method_of (thread_store itsl (stored_tid itsl k)) k

(* for data keys, the value in the store is the same as the value associated with the eac state *)
val lemma_eac_stored_value (#p:pos) (itsl: eac_log p) (k: data_key{is_eac_state_instore itsl k}):
  Lemma (eac_state_value itsl k = stored_value itsl k)

(* 
 * for all keys, the add method stored in the store is the same as the add method associated 
 * with eac state
 *)
val lemma_eac_stored_addm (#p:pos) (itsl: eac_log p) (k:key{is_eac_state_instore itsl k}):
  Lemma (E.add_method_of (eac_state_of_key itsl k) = stored_add_method itsl k)
  
(* if k is in a verifier store, then its eac_state is instore *)
val lemma_instore_implies_eac_state_instore (#p:pos) (itsl:eac_log p) (k:key{k <> Root}) (tid:valid_tid p):
  Lemma (store_contains (thread_store itsl tid) k ==> is_eac_state_instore itsl k)
         
(* the root is always in thread 0 *)
val lemma_root_in_store0 (#p:pos) (itsl: eac_log p):
  Lemma (store_contains (thread_store itsl 0) Root)

val lemma_root_not_in_store (#p:pos) (itsl: eac_log p) (tid:valid_tid p):
  Lemma (not (store_contains (thread_store itsl tid) Root))

(* we use eac constraints to associate a value with each key *)
val eac_value (#p:pos) (itsl: eac_log p) (k:key): value_type_of k

(* eac_value is consistent with stored value *)
val lemma_eac_value_is_stored_value (#p:pos) (itsl: eac_log p) (k:key) (tid: valid_tid p):  
  Lemma (requires (store_contains (thread_store itsl tid) k))
        (ensures (eac_value itsl k = V.stored_value (thread_store itsl tid) k))

val lemma_eac_value_is_evicted_value (#p:pos) (itsl: eac_log p) (k:key):
  Lemma (requires (is_eac_state_evicted itsl k))
        (ensures (eac_state_evicted_value itsl k = eac_state_value itsl k))

val lemma_ext_evict_val_is_stored_val (#p:pos) (itsl: its_log p) (i: seq_index itsl):
  Lemma (requires (is_evict (index itsl i)))
        (ensures (store_contains (thread_store itsl (thread_id_of itsl i)) (key_at itsl i) /\
                  is_evict_ext (vlog_entry_ext_at itsl i) /\
                  V.stored_value (thread_store itsl (thread_id_of itsl i)) (key_at itsl i) = 
                  value_ext (vlog_entry_ext_at itsl i)))

(* if an evict is not the last entry of a key, then there is a add subsequent to the 
 * evict *)
val lemma_evict_has_next_add (#p:pos) (itsl: its_log p) (i:seq_index itsl):
  Lemma (requires (is_evict (index itsl i) /\
                   exists_sat_elems (is_entry_of_key (key_of (index itsl i))) itsl) /\
                   i < last_idx_of_key itsl (key_of (index itsl i)))
        (ensures (has_next_add_of_key itsl i (key_of (index itsl i))))

                  
