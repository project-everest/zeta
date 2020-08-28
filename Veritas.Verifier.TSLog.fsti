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

(* 
 * an indexed sequence log represents and interleaving of a global log (a sequence of thread-level
 * verifier logs. It is a sequence of the form (e,tid) where e denotes a verifier log entry
 * and tid denotes the verifier thread that the entry comes from
 *)
let idx_seq_vlog (p:pos) = seq (idx_elem #vlog_entry p)

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

(* extended time sequence log (with evict values) *)
val time_seq_ext (#p:pos) (itsl: its_log p):
  Tot (le:vlog_ext{project_seq itsl = to_vlog le})

val lemma_its_prefix_ext (#n:pos) (itsl:its_log n) (i:nat{i <= length itsl}):
  Lemma (requires True)
        (ensures (time_seq_ext (prefix itsl i) = prefix (time_seq_ext itsl) i))
        [SMTPat (time_seq_ext (prefix itsl i))]

let is_eac_log (#p:pos) (itsl: its_log p):bool = E.is_eac_log (time_seq_ext itsl)

type eac_ts_log (p:pos) = itsl: its_log p {is_eac_log itsl}
type non_eac_ts_log (p:pos) = itsl: its_log p {not (is_eac_log itsl)}

(* if itsl is eac, then any prefix is also eac *)
val lemma_eac_implies_prefix_eac (#p:pos) (itsl: eac_ts_log p) (i:nat {i <= length itsl}):
  Lemma (requires True)
        (ensures (is_eac_log (prefix itsl i)))
        [SMTPat (prefix itsl i)]

(* the eac state of a key at the end of an its log *)
let eac_state_of_key (#p:pos) (itsl: its_log p) (k:key): eac_state = 
  let tsle = time_seq_ext itsl in 
  let tslek = partn eac_sm k tsle in
  seq_machine_run eac_smk tslek

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

(* the state of a verifier thread after processing entries in a log *)
let verifier_thread_state (#p:pos) (itsl: its_log p) (id:nat{id < p}): (st:vtls{Valid? st}) = 
  let gl = partition_idx_seq itsl in
  assert(VT.verifiable (index (attach_index gl) id));
  t_verify id (index gl id)

(* 
 * when the eac state of a key is Init (no operations on the key yet) no 
 * thread contains the key in its store 
 *)
val lemma_eac_state_init_store 
   (#p:pos) 
   (itsl: eac_ts_log p) (k: key{k <> Root && is_eac_state_init itsl k}) (id:nat{id < p}):
   Lemma (not (store_contains (thread_store (verifier_thread_state itsl id)) k)) 

(* when the eac state of a key is EACEvicted then no thread contains the key in its store *)
val lemma_eac_state_evicted_store (#p:pos) (itsl: eac_ts_log p) 
  (k: key{is_eac_state_evicted itsl k}) (id:nat{id < p}):
  Lemma (not (store_contains (thread_store (verifier_thread_state itsl id)) k))
  
(* when the eac state of a key is "instore" then there is always a previous add *)
val lemma_eac_state_instore_implies_prev_add (#p:pos) (itsl: eac_ts_log p) 
  (k:key{is_eac_state_instore itsl k}):
  Lemma (has_some_add_of_key k (project_seq itsl))

(* when the eac state of a key is instore return the index of the last add that transitioned
 * the key k to "instore" *)
let last_add_idx (#p:pos) (itsl: eac_ts_log p) (k: key{is_eac_state_instore itsl k}): seq_index itsl =
   lemma_eac_state_instore_implies_prev_add itsl k;
   last_index (is_add_of_key k) (project_seq itsl)

(* the verifier thread where the last add of key k happens *)
let last_add_tid (#p:pos) (itsl: eac_ts_log p) (k: key{is_eac_state_instore itsl k}): (tid:nat{tid < p}) =
  snd (index itsl (last_add_idx itsl k))

(* if the eac_state of k is instore, then that k is in the store of the verifier thread of its last add *)
val lemma_eac_state_instore (#p:pos) (itsl: eac_ts_log p) (k:key{is_eac_state_instore itsl k}):
  Lemma (store_contains (thread_store (verifier_thread_state itsl (last_add_tid itsl k))) k /\
         stored_value (thread_store (verifier_thread_state itsl (last_add_tid itsl k))) k = 
         EACInStore?.v (eac_state_of_key itsl k))

val lemma_eac_state_instore_addm (#p:pos) (itsl: eac_ts_log p) (k:key{is_eac_state_instore itsl k}):
  Lemma (is_add (index (project_seq itsl) (last_add_idx itsl k)) /\
         store_contains (thread_store (verifier_thread_state itsl (last_add_tid itsl k))) k /\
         EACInStore?.m (eac_state_of_key itsl k) = 
         addm_of_entry (index (project_seq itsl) (last_add_idx itsl k)) /\
         EACInStore?.m (eac_state_of_key itsl k) = 
         add_method_of (thread_store (verifier_thread_state itsl (last_add_tid itsl k))) k)
  
(* if the eac state of k is instore, then k is not in the store of any verifier thread other than 
 * its last add thread *)
val lemma_eac_state_instore2 (#p:pos) (itsl: eac_ts_log p) 
  (k:key{is_eac_state_instore itsl k}) (id:nat{id < p}):
  Lemma (requires (id <> last_add_tid itsl k))
        (ensures (not (store_contains (thread_store (verifier_thread_state itsl id)) k)))

(* if k is in a verifier store, then its eac_state is instore *)
val lemma_instore_implies_eac_state_instore (#p:pos) (itsl:eac_ts_log p) (k:key{k <> Root}) (tid:nat{tid < p}):
  Lemma (store_contains (thread_store (verifier_thread_state itsl tid)) k ==> is_eac_state_instore itsl k)
         
(* the root is always in thread 0 *)
val lemma_root_in_store0 (#p:pos) (itsl: eac_ts_log p):
  Lemma (store_contains (thread_store (verifier_thread_state itsl 0)) Root)

val lemma_root_not_in_store (#p:pos) (itsl: eac_ts_log p) (tid:pos {tid < p}):
  Lemma (not (store_contains (thread_store (verifier_thread_state itsl tid)) Root))

(* the evicted value is always of the correct type for the associated key *)
val lemma_evict_value_correct_type (#p:pos) (itsl: eac_ts_log p) (k:key{is_eac_state_evicted itsl k}):
  Lemma (is_value_of k (E.value_of (eac_state_of_key itsl k)))

(* 
 * for keys in a thread store, return the value in the thread store; 
 * for other keys return the last evict value or null (init)
 *)
val eac_value (#n:pos) (itsl: eac_ts_log n) (k:key): value_type_of k

val lemma_eac_value_is_stored_value (#p:pos) (itsl: eac_ts_log p) (k:key) (id:nat{id < p}):
  Lemma (requires (store_contains (thread_store (verifier_thread_state itsl id)) k))
        (ensures (eac_value itsl k = 
                  stored_value (thread_store (verifier_thread_state itsl id)) k))

val lemma_eac_value_is_evicted_value (#p:pos) (itsl: eac_ts_log p) (k:key):
  Lemma (requires (is_eac_state_evicted itsl k))
        (ensures (eac_state_evicted_value itsl k = eac_value itsl k))

let key_of (#p:pos) (ie:idx_elem #vlog_entry p): key = 
  let (e,_) = ie in
  V.key_of e

let entry_of_key (k:key) (#p:pos) (ie:idx_elem #vlog_entry p): bool = 
  let (e,_) = ie in
  V.key_of e = k

let has_some_entry_of_key (#p:pos) (itsl: its_log p) (k:key): bool = 
  exists_sat_elems (entry_of_key k) itsl

let its_vlog_entry (#n:pos) (itsl: its_log n) (i:seq_index itsl): vlog_entry =
  fst (index itsl i)

let its_thread_id (#n:pos) (itsl: its_log n) (i:seq_index itsl): (tid:nat{tid < n}) =
  snd (index itsl i)

val lemma_ext_evict_val_is_stored_val (#p:pos) (itsl: its_log p) (i: seq_index itsl):
  Lemma (requires (is_evict (fst (index itsl i))))
        (ensures (is_evict_ext (index (time_seq_ext itsl) i) /\
                  store_contains (thread_store (verifier_thread_state (prefix itsl i)
                                                                      (snd (index itsl i))))
                                 (V.key_of (fst (index itsl i))) /\
                  value_ext (index (time_seq_ext itsl) i) = 
                  stored_value (thread_store (verifier_thread_state (prefix itsl i)
                                                                    (snd (index itsl i))))
                               (V.key_of (fst (index itsl i)))))

let is_of_key (k:key) (#p:pos) (ie:idx_elem #vlog_entry p): bool = 
  let (e,_) = ie in
  V.is_of_key e k

let is_add (#p:pos) (ie:idx_elem #vlog_entry p): bool = 
  let (e,_) = ie in
  V.is_add e

let is_evict (#p:pos) (ie:idx_elem #vlog_entry p): bool = 
  let (e,_) = ie in
  V.is_evict e

(* is the i'th index of itsl a blum add *)
let is_blum_add (#p:nat) (ie:idx_elem #vlog_entry p):bool =
  let (e,_) = ie in
  match e with
  | AddB _ _ _ -> true
  | _ -> false

(* is the index i of ts log an blum evict *)
let is_blum_evict (#p:pos) (ie:idx_elem #vlog_entry p): bool = 
  let (e,_) = ie in
  match e with
  | EvictB _ _ -> true
  | EvictBM _ _ _ -> true
  | _ -> false

let is_add_of_key (k:key) (#p:pos) (ie:idx_elem #vlog_entry p): bool = 
  is_add ie &&
  is_of_key k ie

let is_evict_of_key (k:key) (#p:pos) (ie:idx_elem #vlog_entry p): bool = 
  is_evict ie &&
  is_of_key k ie
  
let has_next_add_of_key (#p:pos) (itsl: its_log p) (i:seq_index itsl) (k:key): bool =
  has_next (is_add_of_key k) itsl i

let next_add_of_key (#p:pos) 
  (itsl: its_log p) 
  (i:seq_index itsl) (k:key{has_next_add_of_key itsl i k}): 
  (j:seq_index itsl{j > i && is_add_of_key k (index itsl j)}) = 
  next_index (is_add_of_key k) itsl i

let last_idx_of_key (#p:pos) (itsl: its_log p) (k:key{has_some_entry_of_key itsl k}):
  seq_index itsl = 
  last_index (entry_of_key k) itsl

(* if an evict is not the last entry of a key, then there is a add subsequent to the 
 * evict *)
val lemma_evict_has_next_add (#p:pos) (itsl: its_log p) (i:seq_index itsl):
  Lemma (requires (is_evict (index itsl i) /\
                   exists_sat_elems (entry_of_key (key_of (index itsl i))) itsl) /\
                   i < last_idx_of_key itsl (key_of (index itsl i)))
        (ensures (has_next_add_of_key itsl i (key_of (index itsl i))))

                  
