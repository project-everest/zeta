module Veritas.Intermediate.VerifySC

open Veritas.Intermediate.Logs
open Veritas.Intermediate.StoreSC

(* These are all independent of the 'verify' function; they should be safe to open *)
open Veritas.BinTree
open Veritas.Hash
open Veritas.Key
open Veritas.MultiSetHash
open Veritas.MultiSetHashDomain
open Veritas.Record
open Veritas.SeqAux

(* It's better not to open these modules to avoid naming conflicts *)
module Spec = Veritas.Verifier
module SpecT = Veritas.Verifier.Thread

(* Thread-local state
   id     : thread id
   st     : thread local store
   clock  : current timestamp
   hadd   : add set hash
   hevict : evict set hash *)
noeq
type vtls =
  | Failed : vtls
  | Valid :
    id : thread_id ->
    st : vstore ->
    clock : timestamp ->
    hadd : ms_hash_value ->
    hevict : ms_hash_value ->
    vtls

let thread_id_of (vs:vtls {Valid? vs}): thread_id = 
  Valid?.id vs

let thread_store (vs: vtls {Valid? vs}): vstore =
  Valid?.st vs

let thread_store_is_map (vs: vtls {Valid? vs}): bool =
  let st = thread_store vs in st.is_map

let thread_store_size (vs: vtls {Valid? vs}): nat =
  let st = thread_store vs in Seq.length st.data

let update_thread_store (vs:vtls {Valid? vs}) (st:vstore) : vtls =
  match vs with
  | Valid id _ clock hadd hevict -> Valid id st clock hadd hevict

let thread_clock (vs:vtls {Valid? vs}) = 
  Valid?.clock vs

let update_thread_clock (vs:vtls {Valid? vs}) (clock:timestamp): vtls = 
  match vs with
  | Valid id st _ hadd hevict -> Valid id st clock hadd hevict

let thread_hadd (vs:vtls {Valid? vs}) = 
  Valid?.hadd vs

let thread_hevict (vs:vtls {Valid? vs}) = 
  Valid?.hevict vs

let update_thread_hadd (vs:vtls {Valid? vs}) (hadd: ms_hash_value): vtls = 
  match vs with
  | Valid id st clock _ hevict -> Valid id st clock hadd hevict

let update_thread_hevict (vs:vtls {Valid? vs}) (hevict:ms_hash_value): vtls = 
  match vs with
  | Valid id st clock hadd _ -> Valid id st clock hadd hevict

val vget (s:slot_id) (k:key) (v:data_value) (vs: vtls {Valid? vs}) : vtls 

val vput (s:slot_id) (k:key) (v:data_value) (vs: vtls {Valid? vs}) : vtls

val vaddm (s:slot_id) (r:record) (s':slot_id) (vs: vtls {Valid? vs}): vtls 

val vevictm (s:slot_id) (s':slot_id) (vs: vtls {Valid? vs}): vtls

val vaddb (s:slot_id) (r:record) (t:timestamp) (j:thread_id) (vs:vtls {Valid? vs}): vtls

val vevictb (s:slot_id) (t:timestamp) (vs:vtls {Valid? vs}): vtls

val vevictbm (s:slot_id) (s':slot_id) (t:timestamp) (vs:vtls {Valid? vs}): vtls

(* Relation between thread-local states *)
let has_failed (vs:vtls) = Failed? vs || not (thread_store_is_map vs)
let vtls_rel (vs:vtls) (vs':Spec.vtls) : Type =
  if has_failed vs then Spec.Failed? vs'
  else 
    match vs, vs' with
    | Valid id st clk ha he, Spec.Valid id' st' clk' _ ha' he' ->
        store_rel st st' /\ 
        // other fields related by equality  
        id = id' /\ clk = clk' /\ ha = ha' /\ he = he'   
    | _, _ -> False

(* Relation between a slot and key *)
let slot_key_rel (vs: vtls {Valid? vs}) (s:slot_id) (k:key) =
  let st = thread_store vs in slot_key_equiv st s k

(* Simulation lemmas for v* functions *)

val lemma_vget_simulates_spec 
      (vs:vtls{Valid? vs})
      (vs':Spec.vtls{Spec.Valid? vs'})
      (s:slot_id)
      (k:data_key)
      (v:data_value)
  : Lemma (requires (vtls_rel vs vs' /\ slot_key_rel vs s k))
          (ensures (vtls_rel (vget s k v vs) (Spec.vget k v vs')))

val lemma_vget_has_failed (vs:vtls{Valid? vs}) (s:slot_id) (k:key) (v:data_value)
  : Lemma (requires (not (thread_store_is_map vs)))
          (ensures (has_failed (vget s k v vs)))

val lemma_vput_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s:slot_id) 
      (k:data_key) 
      (v:data_value) 
  : Lemma (requires (vtls_rel vs vs' /\ slot_key_rel vs s k))
          (ensures (vtls_rel (vput s k v vs) (Spec.vput k v vs'))) 

val lemma_vput_has_failed (vs:vtls{Valid? vs}) (s:slot_id) (k:key) (v:data_value)
  : Lemma (requires (not (thread_store_is_map vs)))
          (ensures (has_failed (vput s k v vs)))

val lemma_vaddm_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s s':slot_id)
      (r:record)
      (k':merkle_key)  
  : Lemma (requires (s < thread_store_size vs /\ 
                     not (store_contains (thread_store vs) s) /\ 
                     vtls_rel vs vs' /\ 
                     slot_key_rel vs s' k'))
          (ensures (vtls_rel (vaddm s r s' vs) (Spec.vaddm r k' vs'))) 

val lemma_vaddm_has_failed (vs:vtls{Valid? vs}) (s s':slot_id) (r:record)
  : Lemma (requires (not (thread_store_is_map vs)))
          (ensures (has_failed (vaddm s r s' vs)))

val lemma_vevictm_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s s':slot_id)
      (k:key)
      (k':merkle_key)  
  : Lemma (requires (vtls_rel vs vs' /\ slot_key_rel vs s k /\ slot_key_rel vs s' k'))
          (ensures (vtls_rel (vevictm s s' vs) (Spec.vevictm k k' vs'))) 

val lemma_vevictm_has_failed (vs:vtls{Valid? vs}) (s s':slot_id)
  : Lemma (requires (not (thread_store_is_map vs)))
          (ensures (has_failed (vevictm s s' vs)))

val lemma_vaddb_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s:slot_id)
      (r:record)
      (t:timestamp)
      (j:thread_id)
  : Lemma (requires (s < thread_store_size vs /\ 
                     not (store_contains (thread_store vs) s) /\ 
                     vtls_rel vs vs'))
          (ensures (vtls_rel (vaddb s r t j vs) (Spec.vaddb r t j vs')))

val lemma_vaddb_has_failed (vs:vtls{Valid? vs}) (s:slot_id) (r:record) (t:timestamp) (j:thread_id)
  : Lemma (requires (not (thread_store_is_map vs)))
          (ensures (has_failed (vaddb s r t j vs)))

val lemma_vevictb_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s:slot_id)
      (k:key)
      (t:timestamp)
  : Lemma (requires (vtls_rel vs vs' /\ slot_key_rel vs s k))
          (ensures (vtls_rel (vevictb s t vs) (Spec.vevictb k t vs'))) 
          [SMTPat (vevictb s t vs); SMTPat (Spec.vevictb k t vs')]
          // note: SMTPat needed for lemma_vevictbm_simulates_spec

val lemma_vevictb_has_failed (vs:vtls{Valid? vs}) (s:slot_id) (t:timestamp)
  : Lemma (requires (not (thread_store_is_map vs)))
          (ensures (has_failed (vevictb s t vs)))

val lemma_vevictbm_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s s':slot_id)
      (k:key)
      (k':merkle_key)
      (t:timestamp)
  : Lemma (requires (vtls_rel vs vs' /\ slot_key_rel vs s k /\ slot_key_rel vs s' k'))
          (ensures (vtls_rel (vevictbm s s' t vs) (Spec.vevictbm k k' t vs'))) 

val lemma_vevictbm_has_failed (vs:vtls{Valid? vs}) (s s':slot_id) (t:timestamp)
  : Lemma (requires (not (thread_store_is_map vs)))
          (ensures (has_failed (vevictbm s s' t vs)))

let t_verify_step (vs:vtls) (e:logS_entry): vtls =
  match vs with
  | Failed -> Failed
  | _ ->
    match e with
    | Get_S s k v -> vget s k v vs
    | Put_S s k v -> vput s k v vs
    | AddM_S s r s' -> vaddm s r s' vs
    | EvictM_S s s' -> vevictm s s' vs
    | AddB_S s r t j -> vaddb s r t j vs
    | EvictB_S s t -> vevictb s t vs
    | EvictBM_S s s' t -> vevictbm s s' t vs

val logS_to_logK_entry (vs:vtls{Valid? vs}) (e:logS_entry) : option logK_entry

let add_to_log (l:option logK) (vs:vtls) (e:logS_entry) : option logK =
  if Some? l && Valid? vs && Some? (logS_to_logK_entry vs e)
  then Some (append1 (Some?.v l) (Some?.v (logS_to_logK_entry vs e)))
  else None

(* Verify a log from a specified initial state; also returns the
   corresponding log with keys *)
let rec t_verify_aux (vs:vtls) (l:logS): Tot (vtls * option logK)
  (decreases (Seq.length l)) =
  let n = Seq.length l in
  if n = 0 then (vs, Some Seq.empty)
  else
    let lp = prefix l (n - 1) in
    let (vsp,lk) = t_verify_aux vs lp in
    let e = Seq.index l (n - 1) in
    let vs' = t_verify_step vsp e in
    let lk' = add_to_log lk vsp e in
    (vs', lk')

val lemma_t_verify_aux_valid_implies_log_exists (vs:vtls) (l:logS)
  : Lemma (requires (Valid? (fst (t_verify_aux vs l))))
          (ensures (Some? (snd (t_verify_aux vs l))))
          (decreases (Seq.length l))
          [SMTPat (Some? (snd (t_verify_aux vs l)))]

(* Main verify function *)
val init_thread_state (id:thread_id): vtls
let t_verify (id:thread_id) (l:logS): vtls = 
  fst (t_verify_aux (init_thread_state id) l) 

let logS_to_logK (id:thread_id) (l:logS{Valid? (t_verify id l)}) : logK =
  Some?.v (snd (t_verify_aux (init_thread_state id) l))

val init_thread_state_valid (id:thread_id)
  : Lemma (Valid? (init_thread_state id))
          [SMTPat (init_thread_state id)]

val lemma_init_thread_state_rel (id:thread_id) :
  Lemma (vtls_rel (init_thread_state id) (Spec.init_thread_state id))

val lemma_t_verify_simulates_spec (id:thread_id) (l:logS) 
  : Lemma (requires (Valid? (t_verify id l)))
          (ensures (vtls_rel (t_verify id l) (Spec.t_verify id (logS_to_logK id l))))

val lemma_logS_to_logK_to_state_op (id:thread_id) (l:logS{Valid? (t_verify id l)})
  : Lemma (ensures (Seq.equal (to_state_op_logS l) 
                              (Veritas.EAC.to_state_op_vlog (logS_to_logK id l))))
