module Veritas.Intermediate.Verify

open Veritas.BinTree
open Veritas.Key
open Veritas.MultiSetHashDomain
open Veritas.Record
open Veritas.SeqAux
open Veritas.Intermediate.SlotKeyRel
open Veritas.Intermediate.Logs
open Veritas.Intermediate.VerifierConfig
open Veritas.Intermediate.Store

module FE = FStar.FunctionalExtensionality
module Spec = Veritas.Verifier
module L = Veritas.Intermediate.Logs
module S = Veritas.Intermediate.Store

(* Thread-local state
   id     : thread id
   st     : thread local store
   clock  : current timestamp
   hadd   : add set hash
   hevict : evict set hash *)
noeq
type vtls vcfg =
  | Failed : vtls vcfg
  | Valid :
    id : thread_id ->
    st : vstore vcfg ->
    clock : timestamp ->
    hadd : ms_hash_value ->
    hevict : ms_hash_value ->
    vtls vcfg

(* get the store of a specified verifier thread *)
let thread_store #vcfg (vs: vtls vcfg {Valid? vs}): vstore _ =
  Valid?.st vs

(* implementation of a verify step that transforms verifier state based on a log entry *)
val verify_step (#vcfg:_) (vs:vtls vcfg) (e:logS_entry vcfg): 
  vtls vcfg

(* once we hit a failed state, we remain there *)
val lemma_verify_failed (#vcfg:_) (vs:vtls vcfg) (e:_)
  : Lemma (requires (Failed? vs))
          (ensures (Failed? (verify_step vs e)))

let rec verify #vcfg (vsinit:vtls vcfg) (l:logS vcfg): Tot (vtls vcfg)
  (decreases (Seq.length l)) =
  let n = Seq.length l in
  if n = 0 then vsinit
  else
    let lp = prefix l (n - 1) in
    let vsp = verify vsinit lp in
    let e = Seq.index l (n - 1) in
    verify_step vsp e

let verifiable #vcfg (vsinit:vtls vcfg) (l:logS _) = 
  Valid? (verify vsinit l)
  
(* if a log is verifiable with some initial state, then that state should be valid *)
val lemma_verifiable_implies_init_valid (#vcfg:_) (vsinit: vtls vcfg) (l: logS _):
  Lemma (requires (verifiable vsinit l))
        (ensures (Valid? vsinit))
        [SMTPat (verifiable vsinit l)]

(* if a log is verifiable then the prefix of the log is verifiable *)
val lemma_verifiable_implies_prefix_verifiable 
      (#vcfg:_) 
      (vsinit: vtls vcfg) 
      (l: logS _{verifiable vsinit l}) 
      (i: seq_index l):
  Lemma (ensures (let li = prefix l i in
                  verifiable vsinit li))
        [SMTPat (verifiable vsinit (prefix l i))]
  
(* verifiability implies consistency of the log *)
val lemma_verifiable_implies_consistent_log (#vcfg:_) (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l}):
  Lemma (ensures (let st = thread_store vsinit in
                  let s2k = to_slot_state_map st in
                  consistent_log s2k l))
        [SMTPat (verifiable vsinit l)]

(* the association of slot -> keys in store is what is mandated by the log *)
val lemma_s2k_store_eq_s2k_log (#vcfg:_) (vsinit: vtls vcfg) (l: logS _{verifiable vsinit l}):
  Lemma (ensures (let stinit = thread_store vsinit in
                  let s2kinit = S.to_slot_state_map stinit in 
                  let stend = thread_store (verify vsinit l) in
                  let s2kend = S.to_slot_state_map stend in
                  let s2klog = L.to_slot_state_map s2kinit l in
                  FE.feq s2kend s2klog))
        [SMTPat (verifiable vsinit l)]

(* the property that slot pointing to implies merkle value pointing to *)
let slot_points_to_is_merkle_points_to_local
  (#vcfg:_) 
  (st: vstore vcfg)
  (s1 s2: slot_id vcfg)
  (d: bin_tree_dir{S.points_to_dir st s1 d s2}) =  
  S.points_to_dir st s1 d s2 ==> 
    (let k1 = stored_key st s1 in
     let k2 = stored_key st s2 in
     is_merkle_key k1 /\
     (let v1 = to_merkle_value (stored_value st s1) in
      mv_points_to v1 d k2))

let slot_points_to_is_merkle_points_to (#vcfg:_) (st: vstore vcfg) = 
  forall (s1 s2: slot_id _). forall d. slot_points_to_is_merkle_points_to_local st s1 s2 d

(* 
 * for any verifiable log, the final state satisfies the property that the slot points to implies 
 * merkle value points to relation
 *)
val lemma_verifiable_implies_slot_is_merkle_points_to (#vcfg:_) (vsinit: vtls vcfg) (l: logS _ {verifiable vsinit l}):
  Lemma (requires (slot_points_to_is_merkle_points_to (thread_store vsinit)))
        (ensures (slot_points_to_is_merkle_points_to (thread_store (verify vsinit l))))
        [SMTPat (verifiable vsinit l)]

(* Relation between thread-local states
   * either both states have Failed
   * or both are Valid with equal contents
     (note that store_rel st st' enforces is_map st) *)
let vtls_rel #vcfg (vs:vtls vcfg) (vs':Spec.vtls) : Type =
  (Failed? vs /\ Spec.Failed? vs') \/
  (Valid? vs /\ Spec.Valid? vs' /\
   (let Valid id st clk ha he = vs in
    let Spec.Valid id' st' clk' _ ha' he' = vs' in
    store_rel st st' /\ id = id' /\ clk = clk' /\ ha = ha' /\ he = he'))

val lemma_vget_simulates_spec 
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (vs':Spec.vtls{Spec.Valid? vs'})      
      (e:logS_entry vcfg{Get_S? e})
  : Lemma (requires (let st = thread_store vs in
                     let s2k = S.to_slot_state_map st in
                     vtls_rel vs vs' /\                     
                     valid_logS_entry s2k e))
          (ensures (let st = thread_store vs in
                    let s2k = S.to_slot_state_map st in
                    let ek = to_logK_entry s2k e in          
                    vtls_rel (verify_step vs e) (Spec.t_verify_step vs' ek)))

val lemma_vget_preserves_ismap
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (e:logS_entry _{Get_S? e})
  : Lemma (requires (S.is_map (thread_store vs)))
          (ensures (Valid? (verify_step vs e) ==> S.is_map (thread_store (verify_step vs e))))

val lemma_vput_simulates_spec 
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (vs':Spec.vtls)      
      (e:logS_entry vcfg{Put_S? e})
  : Lemma (requires (let st = thread_store vs in
                     let s2k = S.to_slot_state_map st in
                     vtls_rel vs vs' /\                     
                     valid_logS_entry s2k e))
          (ensures (let st = thread_store vs in
                    let s2k = S.to_slot_state_map st in
                    let ek = to_logK_entry s2k e in          
                    vtls_rel (verify_step vs e) (Spec.t_verify_step vs' ek)))

val lemma_vput_preserves_ismap
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (e:logS_entry _{Put_S? e})
  : Lemma (requires (S.is_map (thread_store vs)))
          (ensures (Valid? (verify_step vs e) ==> S.is_map (thread_store (verify_step vs e))))

(* adding a key not in store to vaddm preserves the spec relationship *)
val lemma_vaddm_preserves_spec_new_key
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (vs':Spec.vtls)
      (e:logS_entry _{AddM_S? e})
  : Lemma (requires (let st = thread_store vs in
                     let s2k = S.to_slot_state_map st in
                     let AddM_S _ (k,_) _ = e in
                     vtls_rel vs vs' /\
                     valid_logS_entry s2k e /\
                     not (store_contains_key st k)))
          (ensures (let st = thread_store vs in
                    let s2k = S.to_slot_state_map st in
                    let ek = to_logK_entry s2k e in
                    vtls_rel (verify_step vs e) (Spec.t_verify_step vs' ek)))

(* if the key is not present in store and store is a map, then store remains a map after add *)
val lemma_vaddm_preserves_ismap_new_key
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (e:logS_entry _{AddM_S? e})
  : Lemma (requires (let st = thread_store vs in
                     let AddM_S _ (k,_) _ = e in
                     not (store_contains_key st k)))
          (ensures (Valid? (verify_step vs e) ==> S.is_map (thread_store (verify_step vs e))))

(* addb preserves spec relationship if the kew is not in store *)
val lemma_vaddb_preserves_spec_new_key
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (vs':Spec.vtls)      
      (e:logS_entry _{AddB_S? e})
  : Lemma (requires (let st = thread_store vs in
                     let s2k = S.to_slot_state_map st in
                     let AddB_S _ (k,_) _ _ = e in
                     vtls_rel vs vs' /\
                     valid_logS_entry s2k e /\
                     not (store_contains_key st k)))
          (ensures (let st = thread_store vs in
                    let s2k = S.to_slot_state_map st in
                    let ek = to_logK_entry s2k e in
                    vtls_rel (verify_step vs e) (Spec.t_verify_step vs' ek)))

(* if the key is not present in store and store is a map, then store remains a map after add *)
val lemma_vaddb_preserves_ismap_new_key
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (e:logS_entry _{AddB_S? e})
  : Lemma (requires (let st = thread_store vs in
                     let AddB_S _ (k,_) _ _ = e in
                     not (store_contains_key st k)))
          (ensures (Valid? (verify_step vs e) ==> S.is_map (thread_store (verify_step vs e))))

val lemma_evictb_simulates_spec 
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (vs':Spec.vtls)      
      (e:logS_entry vcfg{EvictB_S? e})
  : Lemma (requires (let st = thread_store vs in
                     let s2k = S.to_slot_state_map st in
                     vtls_rel vs vs' /\                     
                     valid_logS_entry s2k e))
          (ensures (let st = thread_store vs in
                    let s2k = S.to_slot_state_map st in
                    let ek = to_logK_entry s2k e in          
                    vtls_rel (verify_step vs e) (Spec.t_verify_step vs' ek)))

val lemma_evictb_preserves_ismap
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (e:logS_entry _{EvictB_S? e})
  : Lemma (requires (S.is_map (thread_store vs)))
          (ensures (Valid? (verify_step vs e) ==> S.is_map (thread_store (verify_step vs e))))
  
val lemma_evictm_simulates_spec
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (vs':Spec.vtls)      
      (e:logS_entry vcfg{EvictM_S? e})
  : Lemma (requires (let st = thread_store vs in
                     let s2k = S.to_slot_state_map st in
                     vtls_rel vs vs' /\                     
                     valid_logS_entry s2k e /\
                     slot_points_to_is_merkle_points_to st))
          (ensures (let st = thread_store vs in
                    let s2k = S.to_slot_state_map st in
                    let ek = to_logK_entry s2k e in          
                    vtls_rel (verify_step vs e) (Spec.t_verify_step vs' ek)))  

val lemma_evictm_preserves_ismap
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (e:logS_entry _{EvictM_S? e})
  : Lemma (requires (S.is_map (thread_store vs)))
          (ensures (Valid? (verify_step vs e) ==> S.is_map (thread_store (verify_step vs e))))

val lemma_evictbm_simulates_spec
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (vs':Spec.vtls)      
      (e:logS_entry vcfg{EvictBM_S? e})
  : Lemma (requires (let st = thread_store vs in
                     let s2k = S.to_slot_state_map st in
                     vtls_rel vs vs' /\                     
                     valid_logS_entry s2k e /\
                     slot_points_to_is_merkle_points_to st))
          (ensures (let st = thread_store vs in
                    let s2k = S.to_slot_state_map st in
                    let ek = to_logK_entry s2k e in          
                    vtls_rel (verify_step vs e) (Spec.t_verify_step vs' ek)))  

val lemma_evictbm_preserves_ismap
      (#vcfg:_)
      (vs:vtls vcfg{Valid? vs})
      (e:logS_entry _{EvictBM_S? e})
  : Lemma (requires (S.is_map (thread_store vs)))
          (ensures (Valid? (verify_step vs e) ==> S.is_map (thread_store (verify_step vs e))))

(*



let t_verify_step #vcfg (vs:vtls vcfg) (e:logS_entry vcfg): vtls vcfg =
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

(* Convert slot-based log entry e to a key-based log entry, given verifier state vs.
   This is basically a "light" version of the vfun functions that reconstructs the log. 
   We could have the vfun functions return logK entries instead, but this seems cleaner. *)
let logS_to_logK_entry #vcfg (vs:vtls vcfg {Valid? vs}) (e:logS_entry vcfg) : option logK_entry =
  let st = thread_store vs in
  match e with
  | Get_S s k v -> 
      if inuse_slot st s && k = stored_key st s
      then Some (Spec.Get k v) else None
  | Put_S s k v -> 
      if inuse_slot st s && k = stored_key st s
      then Some (Spec.Put k v) else None
  | AddM_S _ r s' -> 
      if inuse_slot st s' && is_merkle_key (stored_key st s') 
      then Some (Spec.AddM r (stored_key st s')) else None
  | EvictM_S s s' -> 
      if inuse_slot st s && inuse_slot st s' && is_merkle_key (stored_key st s') 
      then Some (Spec.EvictM (stored_key st s) (stored_key st s')) else None
  | AddB_S _ r t j -> 
      Some (Spec.AddB r t j)
  | EvictB_S s t -> 
      if inuse_slot st s
      then Some (Spec.EvictB (stored_key st s) t) else None
  | EvictBM_S s s' t ->
      if inuse_slot st s && inuse_slot st s' && is_merkle_key (stored_key st s') 
      then Some (Spec.EvictBM (stored_key st s) (stored_key st s') t) else None

(* Add the logK_entry equivalent of e to log l, given current state vs. *)
let add_to_log #vcfg (l:option logK) (vs:vtls vcfg) (e:logS_entry vcfg) : option logK =
  if Some? l && Valid? vs && Some? (logS_to_logK_entry vs e)
  then Some (append1 (Some?.v l) (Some?.v (logS_to_logK_entry vs e)))
  else None

(* Verify a log from a specified initial state. *)
let rec t_verify_aux #vcfg (vs:vtls vcfg) (l:logS vcfg): Tot ((vtls vcfg) * option logK)
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

val lemma_t_verify_aux_valid_implies_log_exists (#vcfg:_) (vs:vtls vcfg) (l:logS vcfg)
  : Lemma (requires (Valid? (fst (t_verify_aux vs l))))
          (ensures (Some? (snd (t_verify_aux vs l))))
          (decreases (Seq.length l))
          [SMTPat (Some? (snd (t_verify_aux vs l)))]

let init_thread_state #vcfg (id:thread_id): vtls vcfg = 
  let vs = Valid id (empty_store vcfg) (MkTimestamp 0 0) empty_hash_value empty_hash_value in  
  if id = 0 then
    let st0 = thread_store vs in
    let st0_upd = madd_to_store_root st0 0 (init_value Root) in
    update_thread_store vs st0_upd    
  else vs

let init_thread_state2 #vcfg (id:thread_id): vtls vcfg = 
  let vs = Valid id (empty_store vcfg) (MkTimestamp 0 0) empty_hash_value empty_hash_value in  
  if id = 0 then
    let st0 = thread_store vs in
    let st0_upd = madd_to_store_root st0 0 (init_value Root) in
    update_thread_store vs st0_upd    
  else vs


(* Main thread-level verify function *)
let t_verify #vcfg (id:thread_id) (l:logS vcfg): vtls vcfg = 
  fst (t_verify_aux (init_thread_state id) l) 

let logS_to_logK #vcfg (id:thread_id) (l:logS vcfg{Valid? (t_verify id l)}) : logK =
  Some?.v (snd (t_verify_aux (init_thread_state #vcfg id) l))

let init_thread_state_valid #vcfg (id:thread_id)
  : Lemma (Valid? (init_thread_state #vcfg id))
          [SMTPat (init_thread_state #vcfg id)]
  = ()

(** Utilities for running a single verifier thread.
    Follows the definitions in Veritas.Verifier.Thread. **)

let verify #vcfg (tl:thread_id_logS vcfg): vtls _ =
  t_verify (fst tl) (snd tl)

let tl_verifiable #vcfg (tl: thread_id_logS vcfg): bool =
  Valid? (verify tl)

let tl_verifiable_log #vcfg = tl: thread_id_logS vcfg {tl_verifiable tl}

val lemma_tl_verifiable_implies_prefix_verifiable
  (#vcfg:_) (tl:tl_verifiable_log #vcfg) (i:nat{i <= tl_length tl}):
  Lemma (ensures (tl_verifiable (tl_prefix tl i)))

let tl_clock #vcfg (tl:tl_verifiable_log #vcfg) (i:tl_idx tl): timestamp =
  let vs = verify #vcfg (tl_prefix tl (i + 1)) in
  lemma_tl_verifiable_implies_prefix_verifiable tl (i + 1);
  Valid?.clock (verify #vcfg (tl_prefix tl (i + 1)))

let tl_verify #vcfg (tl:thread_id_logS vcfg) (i:tl_idx tl): vtls _ =
  verify (tl_prefix tl (i + 1))

(* Utilities for running all verifier threads and comparing aggregate add/evict hashes.
   Follows the definitions in Veritas.Verifier.Global. *) 
let gl_verifiable #vcfg (gl: g_logS vcfg) = 
  forall (tid:seq_index gl). tl_verifiable (thread_log gl tid)

let gl_verifiable_log vcfg = gl:g_logS vcfg{gl_verifiable gl}

val lemma_gl_verifiable_implies_prefix_verifiable
  (#vcfg:_) (gl:gl_verifiable_log vcfg) (i:nat{i <= Seq.length gl}):
  Lemma (ensures (gl_verifiable #vcfg (prefix gl i)))
        [SMTPat (prefix gl i)]

let rec hadd_aux #vcfg (gl: gl_verifiable_log vcfg)
  : Tot (ms_hash_value)
    (decreases (Seq.length gl)) 
  = let p = Seq.length gl in
    if p = 0 then empty_hash_value
    else
      let gl' = prefix gl (p - 1) in
      let h1 = hadd_aux gl' in
      let h2 = thread_hadd (verify (thread_log gl (p - 1))) in
      ms_hashfn_agg h1 h2

let hadd #vcfg (gl: gl_verifiable_log vcfg): ms_hash_value = hadd_aux gl

let rec hevict_aux #vcfg (gl: gl_verifiable_log vcfg)
  : Tot (ms_hash_value)
    (decreases (Seq.length gl))
  = let p = Seq.length gl in
    if p = 0 then empty_hash_value
    else
      let gl' = prefix gl (p - 1) in
      let h1 = hevict_aux gl' in
      let h2 = thread_hevict (verify (thread_log gl (p - 1))) in
      ms_hashfn_agg h1 h2

let hevict #vcfg (gl: gl_verifiable_log vcfg): ms_hash_value = hevict_aux gl

let gl_hash_verifiable #vcfg (gl: gl_verifiable_log vcfg): bool = 
  hadd gl = hevict gl

let gl_hash_verifiable_log vcfg = gl:gl_verifiable_log vcfg{gl_hash_verifiable gl}

let gl_clock #vcfg (gl:gl_verifiable_log vcfg) (i:I.sseq_index gl): timestamp = 
  let (tid, idx) = i in  
  let tl = thread_log gl tid in
  tl_clock tl idx

let gl_verify #vcfg (gl:g_logS vcfg) (i:I.sseq_index gl): vtls _ =
  let (tid, idx) = i in  
  let tl = thread_log gl tid in
  tl_verify tl idx

(* Utilities for verifying the global, interleaved log shared among all threads.
   Follows the definitions in Veritas.Verifier.TSLog. *) 

let il_verifiable #vcfg (il: il_logS vcfg) = 
  gl_verifiable (g_logS_of il)

let il_clock #vcfg (il: il_logS vcfg{il_verifiable il}) (i: I.seq_index il): timestamp =
  let gl = g_logS_of il in
  let j = I.i2s_map il i in
  gl_clock gl j

(* state at thread j after processing log entry i (which modifies the state of j) *)
let il_verify #vcfg (il: il_logS vcfg) (i: I.seq_index il): vtls _ =
  let gl = g_logS_of il in
  let j = I.i2s_map il i in
  gl_verify gl j

val clock_sorted (#vcfg:_) (il: il_logS vcfg {il_verifiable il}): prop

let its_log vcfg = il:il_logS vcfg{il_verifiable il /\ clock_sorted il}

let il_hash_verifiable #vcfg (itsl: its_log vcfg) = gl_hash_verifiable (g_logS_of itsl)

let il_hash_verifiable_log vcfg = itsl:its_log vcfg{il_hash_verifiable itsl}

val lemma_prefix_verifiable (#vcfg:_) (itsl: its_log vcfg) (i:nat{i <= I.length itsl}):
  Lemma (ensures (il_verifiable (I.prefix itsl i) /\ clock_sorted (I.prefix itsl i)))
        [SMTPat (I.prefix itsl i)]

// final correctness property
val lemma_verifier_correct (#vcfg:_) (gl: gl_hash_verifiable_log vcfg { ~ (seq_consistent (to_state_op_glogS gl))})
  : hash_collision_gen 

*)
