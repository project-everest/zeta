module Veritas.Intermediate.VerifySKC

open Veritas.Intermediate.Logs
open Veritas.Intermediate.StoreSKC

module FE = FStar.FunctionalExtensionality

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

val vget (s:slot_id) (v:data_value) (vs: vtls {Valid? vs}) : vtls 

val vput (s:slot_id) (v:data_value) (vs: vtls {Valid? vs}) : vtls

val vaddm (s:slot_id) (r:record) (s':slot_id) (vs: vtls {Valid? vs}): vtls 

val vevictm (s:slot_id) (s':slot_id) (vs: vtls {Valid? vs}): vtls

val vaddb (s:slot_id) (r:record) (t:timestamp) (j:thread_id) (vs:vtls {Valid? vs}): vtls

val vevictb (s:slot_id) (t:timestamp) (vs:vtls {Valid? vs}): vtls

val vevictbm (s:slot_id) (s':slot_id) (t:timestamp) (vs:vtls {Valid? vs}): vtls

(* Relation between stores *)
let store_rel (st:vstore) (st':Spec.vstore) : Type = 
  st.is_map /\ FE.feq st' (as_map st)

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
          (ensures (vtls_rel (vget s v vs) (Spec.vget k v vs')))

val lemma_vget_has_failed (vs:vtls{Valid? vs}) (s:slot_id) (v:data_value)
  : Lemma (requires (not (thread_store_is_map vs)))
          (ensures (has_failed (vget s v vs)))

val lemma_vput_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s:slot_id) 
      (k:data_key) 
      (v:data_value) 
  : Lemma (requires (vtls_rel vs vs' /\ slot_key_rel vs s k))
          (ensures (vtls_rel (vput s v vs) (Spec.vput k v vs'))) 

val lemma_vput_has_failed (vs:vtls{Valid? vs}) (s:slot_id) (v:data_value)
  : Lemma (requires (not (thread_store_is_map vs)))
          (ensures (has_failed (vput s v vs)))

val lemma_vaddm_simulates_spec 
      (vs:vtls{Valid? vs}) 
      (vs':Spec.vtls{Spec.Valid? vs'}) 
      (s s':slot_id)
      (r:record)
      (k':merkle_key)  
  : Lemma (requires (vtls_rel vs vs') /\ slot_key_rel vs s' k')
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
  : Lemma (requires (vtls_rel vs vs'))
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

(* Note that the key values aren't used in the v* functions -
   they are just useful (maybe?) for proof *)
let t_verify_step (vs:vtls) (e:logSK_entry): vtls =
  match vs with
  | Failed -> Failed
  | _ ->
    match e with
    | Get_SK s _ v -> vget s v vs
    | Put_SK s _ v -> vput s v vs
    | AddM_SK s r s' _  -> vaddm s r s' vs
    | EvictM_SK s _ s' _ -> vevictm s s' vs
    | AddB_SK s r t j -> vaddb s r t j vs
    | EvictB_SK s _ t -> vevictb s t vs
    | EvictBM_SK s _ s' _ t -> vevictbm s s' t vs

(* Verify a log from a specified initial state *)
let rec t_verify_aux (vs:vtls) (l:logSK): Tot vtls
  (decreases (Seq.length l)) =
  let n = Seq.length l in
  if n = 0 then vs
  else
    let l' = prefix l (n - 1) in
    let vs' = t_verify_aux vs l' in
    let e' = Seq.index l (n - 1) in
    t_verify_step vs' e'

(* Main verify function *)
val init_thread_state (id:thread_id): vtls
let t_verify (id:thread_id) (l:logSK): vtls = 
  t_verify_aux (init_thread_state id) l 

let verify (id:thread_id) (l:logSK): vtls =
  let vs = t_verify id l in
  if Valid? vs
  then if thread_store_is_map vs then vs else Failed
  else Failed

let verifiable (id:thread_id) (l: logSK): bool =
  Valid? (verify id l)

val init_thread_state_valid (id:thread_id)
  : Lemma (Valid? (init_thread_state id))
          [SMTPat (init_thread_state id)]

val lemma_init_thread_state_rel (id:thread_id) :
  Lemma (vtls_rel (init_thread_state id) (Spec.init_thread_state id))

(* Relation between logs -- haven't really worked this out yet *)
let log_rel  (l:logSK) (l':logK) : Type 
  = skc l /\ drop_slots l = l'

// whatever the defn of log_rel, it should satisfy lemma_log_rel
let log_entry_rel (vs:vtls{Valid? vs}) (e:logSK_entry) (e':logK_entry) : Type
  = match e, e' with
    | Get_SK s _ v, Spec.Get k v' -> slot_key_rel vs s k /\ v = v'
    | Put_SK s _ v, Spec.Put k v' -> slot_key_rel vs s k /\ v = v'
    | AddM_SK s r s' _, Spec.AddM r' k' -> r = r' /\ slot_key_rel vs s' k'
    | EvictM_SK s _ s' _, Spec.EvictM k k' -> slot_key_rel vs s k /\ slot_key_rel vs s' k'
    | AddB_SK s r t j, Spec.AddB r' t' j' -> r = r' /\ t = t' /\ j = j' 
    | EvictB_SK s _ t, Spec.EvictB k t' -> slot_key_rel vs s k /\ t = t'
    | EvictBM_SK s _ s' _ t, Spec.EvictBM k k' t' -> slot_key_rel vs s k /\ slot_key_rel vs s' k' /\ t = t'
    | _, _ -> False

let log_rel_with_vtls (vs:vtls{Valid? vs}) (l:logSK) (l':logK) : Type 
  = Seq.length l = Seq.length l' /\
    (forall (i:seq_index l). 
       let vs2 = t_verify_aux vs (prefix l i) in
       Valid? vs2 ==>
       log_entry_rel vs2 (Seq.index l i) (Seq.index l' i))

let lemma_log_rel (l:logSK) (l':logK) 
  : Lemma (requires (log_rel l l'))
          (ensures (forall (id:thread_id). log_rel_with_vtls (init_thread_state id) l l')) 
  = admit()

val lemma_t_verify_simulates_spec (id:thread_id) (l:logSK) (l':logK)
  : Lemma (requires (log_rel l l'))
          (ensures (vtls_rel (t_verify id l) (Spec.t_verify id l')))

(* For any log, the intermediate implementation will verify 
   iff the the spec implementation does. *)

let lemma_verifiable_simulates_spec (id:thread_id) (l:logSK) (l':logK)
  : Lemma (requires (log_rel l l'))
          (ensures (let tl : SpecT.thread_id_vlog = (id,l') in
                    verifiable id l = SpecT.verifiable tl))
  = lemma_t_verify_simulates_spec id l l';
    let vs = t_verify id l in
    if Valid? vs
    then if not (thread_store_is_map vs) 
    then admit()
