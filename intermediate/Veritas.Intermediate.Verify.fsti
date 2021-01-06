module Veritas.Intermediate.Verify

open Veritas.Intermediate.Logs
open Veritas.Intermediate.VerifierConfig
open Veritas.Intermediate.Store

(* These are all independent of the 'verify' function; they should be safe to open *)
open Veritas.BinTree
open Veritas.Hash
open Veritas.Key
open Veritas.MultiSetHash
open Veritas.MultiSetHashDomain
open Veritas.Record
open Veritas.SeqAux
open Veritas.SeqMachine
open Veritas.State
open Veritas.StateSeqMachine
open Veritas.Verifier.EAC

(* It's better not to open these modules to avoid naming conflicts *)
module I = Veritas.Interleave
module Spec = Veritas.Verifier
module SpecC = Veritas.Verifier.Correctness
module SpecG = Veritas.Verifier.Global
module SpecT = Veritas.Verifier.Thread
module SpecTS = Veritas.Verifier.TSLog

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

let thread_id_of #vcfg (vs:vtls vcfg{Valid? vs}): thread_id = 
  Valid?.id vs

let thread_store #vcfg (vs: vtls vcfg {Valid? vs}): vstore _ =
  Valid?.st vs

let thread_store_size #vcfg (vs: vtls vcfg {Valid? vs}): nat =
  let st = thread_store vs in Seq.length st

let update_thread_store #vcfg (vs:vtls vcfg {Valid? vs}) (st:vstore vcfg) : vtls _ =
  match vs with
  | Valid id _ clock hadd hevict -> Valid id st clock hadd hevict

let thread_clock #vcfg (vs:vtls vcfg {Valid? vs}) = 
  Valid?.clock vs

let update_thread_clock #vcfg (vs:vtls vcfg {Valid? vs}) (clock:timestamp): vtls _ = 
  match vs with
  | Valid id st _ hadd hevict -> Valid id st clock hadd hevict

let thread_hadd #vcfg (vs:vtls vcfg {Valid? vs}) = 
  Valid?.hadd vs

let thread_hevict #vcfg (vs:vtls vcfg {Valid? vs}) = 
  Valid?.hevict vs

let update_thread_hadd #vcfg (vs:vtls vcfg {Valid? vs}) (hadd: ms_hash_value): vtls _ = 
  match vs with
  | Valid id st clock _ hevict -> Valid id st clock hadd hevict

let update_thread_hevict #vcfg (vs:vtls vcfg {Valid? vs}) (hevict:ms_hash_value): vtls _ = 
  match vs with
  | Valid id st clock hadd _ -> Valid id st clock hadd hevict

let vget #vcfg (s:slot_id vcfg) (k:data_key) (v:data_value) (vs: vtls vcfg {Valid? vs}) : vtls vcfg =
  let st = thread_store vs in
  (* check slot s is not empty *)
  if empty_slot st s then Failed
  (* check stored key and value *)
  else let k' = stored_key st s in
       let v' = stored_value st s in
       if k <> k' then Failed
       else if to_data_value v' <> v then Failed
       else vs

let vput #vcfg (s:slot_id vcfg) (k:data_key) (v:data_value) (vs: vtls vcfg {Valid? vs}) : vtls vcfg =
  let st = thread_store vs in
  (* check slot s is not empty *)
  if empty_slot st s then Failed
  (* check stored key is k *)
  else let k' = stored_key st s in
       if k <> k' then Failed
       else update_thread_store vs (update_data_value st s v)

let vaddm #vcfg (s:slot_id vcfg) (r:record) (s':slot_id vcfg) (vs: vtls vcfg {Valid? vs}): vtls vcfg =
  let st = thread_store vs in
  let (k,v) = r in
  (* check slot s' is not empty *)
  if empty_slot st s' then Failed
  else
    let k' = stored_key st s' in
    let v' = stored_value st s' in
    (* check k is a proper desc of k' *)
    if not (is_proper_desc k k') then Failed
    (* check slot s is empty *)
    else if inuse_slot st s then Failed
    (* check type of v is consistent with k *)
    else if not (is_value_of k v) then Failed
    else
      let v' = to_merkle_value v' in
      let d = desc_dir k k' in
      let dh' = desc_hash_dir v' d in
      let h = hashfn v in
      match dh' with
      | Empty -> (* k' has no child in direction d *)
        if v <> init_value k then Failed
        else
          let st_upd = add_to_store st s k v Spec.MAdd in
          let v'_upd = Spec.update_merkle_value v' d k h false in
          let st_upd = update_empty_merkle_value st_upd s' d s v'_upd in
          update_thread_store vs st_upd
      | Desc k2 h2 b2 ->
        if k2 = k then (* k is a child of k' *)
          (* check hashes match and k was not evicted to blum *)
          if not (h2 = h && b2 = false) then Failed
          (* check slot s' does not contain a desc along direction d *)
          else if desc_in_store st s' d then Failed
          else
            let st_upd = add_to_store st s k v Spec.MAdd in
            let st_upd = add_desc_slot st_upd s' d s in
            update_thread_store vs st_upd
        else (* otherwise, k is not a child of k' *)
          (* first add must be init value *)
          if v <> init_value k then Failed
          (* check k2 is a proper desc of k *)
          else if not (is_proper_desc k2 k) then Failed
          else
            let d2 = desc_dir k2 k in
            let mv = to_merkle_value v in
            let mv_upd = Spec.update_merkle_value mv d2 k2 h2 b2 in
            let v'_upd = Spec.update_merkle_value v' d k h false in
            assert(mv_points_to_some mv_upd d2);
            if desc_in_store st s' d then (
              admit()
            )
            else 
              let st_upd = add_to_store st s k (MVal mv_upd) Spec.MAdd in
              let st_upd = update_merkle_value st_upd s' d k h false s in
              update_thread_store vs st_upd

let has_instore_merkle_desc (st:vstore) (s:slot_id{store_contains st s}): bool = 
  let k = stored_key st s in
  if is_data_key k then false
  else 
    let v = to_merkle_value (stored_value_by_key st k) in
    let ld = desc_hash_dir v Left in
    let rd = desc_hash_dir v Right in
    Desc? ld && in_store_bit st s Left || Desc? rd && in_store_bit st s Right

let vevictm (s:slot_id) (s':slot_id) (vs: vtls {Valid? vs}): vtls = 
  let st = thread_store vs in
  (* check store contains s and s' *)
  if not (store_contains st s && store_contains st s') then Failed
  else 
    let k = stored_key st s in
    let v = stored_value st s in
    let k' = stored_key st s' in
    let v' = stored_value st s' in
    (* check k is a proper descendent of k' *)
    if not (is_proper_desc k k') then Failed
    (* check k does not have a (merkle) child in the store *)
    else if has_instore_merkle_desc st s then Failed
    else
      let d = desc_dir k k' in
      let v' = to_merkle_value v' in
      let dh' = desc_hash_dir v' d in
      let h = hashfn v in
      match dh' with
      | Empty -> Failed
      | Desc k2 h2 b2 -> 
          if k2 <> k then Failed
          else
            let v'_upd = Spec.update_merkle_value v' d k h false in
            let st_upd = update_value st s' (MVal v'_upd) in
            let st_upd2 = evict_from_store st_upd s in
            let st_upd3 = update_in_store st_upd2 s' d false in
            update_thread_store vs st_upd3

let vaddb (s:slot_id) (r:record) (t:timestamp) (j:thread_id) (vs:vtls {Valid? vs}): vtls = 
  if not (s < thread_store_size vs) then Failed
  else
    let st = thread_store vs in 
    let (k,v) = r in
    (* check value type consistent with key k *)
    if not (is_value_of k v) then Failed
    (* check store contains slot s *)
    else if store_contains st s then Failed
    else 
      (* update add hash *)
      let h = thread_hadd vs in
      let h_upd = ms_hashfn_upd (MHDom (k,v) t j) h in
      let vs_upd = update_thread_hadd vs h_upd in
      (* update clock *)
      let clk = thread_clock vs in
      let clk_upd = Spec.max clk (next t) in
      let vs_upd2 = update_thread_clock vs_upd clk_upd in
      (* add record to store *)
      let st_upd = add_to_store st s k v Spec.BAdd in
      update_thread_store vs_upd2 st_upd

let vevictb_aux (s:slot_id) (t:timestamp) (eam:add_method) (vs:vtls {Valid? vs}): vtls = 
  let clock = thread_clock vs in
  let st = thread_store vs in
  (* check store contains slot s *)
  if not (store_contains st s) then Failed
  else
    let k = stored_key st s in
    let v = stored_value st s in
    (* check key at s is not root *)
    if k = Root then Failed
    (* check time of evict < current time *)
    else if not (ts_lt clock t) then Failed
    (* check s was added through blum *)  
    else if add_method_of st s <> eam then Failed
    (* check k has no (merkle) children n the store *)
    else if has_instore_merkle_desc st s then Failed  
    else 
      (* update evict hash *)
      let h = thread_hevict vs in
      let h_upd = ms_hashfn_upd (MHDom (k,v) t (thread_id_of vs)) h in
      let vs_upd = update_thread_hevict vs h_upd in
      (* update clock *)
      let vs_upd2 = update_thread_clock vs_upd t in    
      (* evict record *)
      let st_upd = evict_from_store st s in
      update_thread_store vs_upd2 st_upd

let vevictb (s:slot_id) (t:timestamp) (vs:vtls {Valid? vs}): vtls = 
  vevictb_aux s t Spec.BAdd vs

let vevictbm (s:slot_id) (s':slot_id) (t:timestamp) (vs:vtls {Valid? vs}): vtls = 
  let st = thread_store vs in
  (* check store contains s and s' *)
  if not (store_contains st s && store_contains st s') then Failed
  else
    let k = stored_key st s in
    let k' = stored_key st s' in
    let v' = stored_value st s' in
    (* check k is a proper desc of k' *)
    if not (is_proper_desc k k') then Failed
    (* check s was added through merkle *)
    else if add_method_of st s <> Spec.MAdd then Failed  
    (* check k has no (merkle) children in the store *)
    else if has_instore_merkle_desc st s then Failed  
    else
      let v' = to_merkle_value v' in
      let d = desc_dir k k' in
      let dh' = desc_hash_dir v' d in
      match dh' with
      | Empty -> Failed
      | Desc k2 h2 b2 -> 
          if k2 <> k || b2 then Failed
          else
            let v'_upd = Spec.update_merkle_value v' d k h2 true in
            let st_upd = update_value st s' (MVal v'_upd) in
            let st_upd2 = update_in_store st_upd s' d false in
            vevictb_aux s t Spec.MAdd (update_thread_store vs st_upd2)

(* Relation between thread-local states
   * either both states have Failed
   * or both are Valid with equal contents
     (note that store_rel st st' enforces is_map st) *)
let vtls_rel (vs:vtls) (vs':Spec.vtls) : Type =
  (Failed? vs /\ Spec.Failed? vs') \/
  (Valid? vs /\ Spec.Valid? vs' /\
   (let Valid id st clk ha he = vs in
    let Spec.Valid id' st' clk' _ ha' he' = vs' in
    store_rel st st' /\ id = id' /\ clk = clk' /\ ha = ha' /\ he = he'))

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

(* Convert slot-based log entry e to a key-based log entry, given verifier state vs.
   This is basically a "light" version of the vfun functions that reconstructs the log. 
   We could have the vfun functions return logK entries instead, but this seems cleaner. *)
let logS_to_logK_entry (vs:vtls{Valid? vs}) (e:logS_entry) : option logK_entry =
  let st = thread_store vs in
  match e with
  | Get_S s k v -> 
      if store_contains st s && k = stored_key st s
      then Some (Spec.Get k v) else None
  | Put_S s k v -> 
      if store_contains st s && k = stored_key st s
      then Some (Spec.Put k v) else None
  | AddM_S _ r s' -> 
      if store_contains st s' && is_merkle_key (stored_key st s') 
      then Some (Spec.AddM r (stored_key st s')) else None
  | EvictM_S s s' -> 
      if store_contains st s && store_contains st s' && is_merkle_key (stored_key st s') 
      then Some (Spec.EvictM (stored_key st s) (stored_key st s')) else None
  | AddB_S _ r t j -> 
      Some (Spec.AddB r t j)
  | EvictB_S s t -> 
      if store_contains st s
      then Some (Spec.EvictB (stored_key st s) t) else None
  | EvictBM_S s s' t ->
      if store_contains st s && store_contains st s' && is_merkle_key (stored_key st s') 
      then Some (Spec.EvictBM (stored_key st s) (stored_key st s') t) else None

(* Add the logK_entry equivalent of e to log l, given current state vs. *)
let add_to_log (l:option logK) (vs:vtls) (e:logS_entry) : option logK =
  if Some? l && Valid? vs && Some? (logS_to_logK_entry vs e)
  then Some (append1 (Some?.v l) (Some?.v (logS_to_logK_entry vs e)))
  else None

(* Verify a log from a specified initial state. *)
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

(* Initialize verifier state *)
// TODO: what should the initial size be?
let store_size = 65536 // 2 ^ 16
let init_thread_state (id:thread_id): vtls = 
  let vs = Valid id (empty_store store_size) (MkTimestamp 0 0) empty_hash_value empty_hash_value in  
  if id = 0 then
    let st0 = thread_store vs in
    let st0_upd = add_to_store st0 0 Root (init_value Root) Spec.MAdd in
    update_thread_store vs st0_upd    
  else vs

(* Main thread-level verify function *)
let t_verify (id:thread_id) (l:logS): vtls = 
  fst (t_verify_aux (init_thread_state id) l) 

let logS_to_logK (id:thread_id) (l:logS{Valid? (t_verify id l)}) : logK =
  Some?.v (snd (t_verify_aux (init_thread_state id) l))

let init_thread_state_valid (id:thread_id)
  : Lemma (Valid? (init_thread_state id))
          [SMTPat (init_thread_state id)]
  = ()

(** Utilities for running a single verifier thread.
    Follows the definitions in Veritas.Verifier.Thread. **)

let verify (tl:thread_id_logS): vtls =
  t_verify (fst tl) (snd tl)
  
let tl_verifiable (tl: thread_id_logS): bool =
  Valid? (verify tl)

let tl_verifiable_log = tl: thread_id_logS {tl_verifiable tl}

val lemma_tl_verifiable_implies_prefix_verifiable
  (tl:tl_verifiable_log) (i:nat{i <= tl_length tl}):
  Lemma (ensures (tl_verifiable (tl_prefix tl i)))
        [SMTPat (tl_prefix tl i)]

let tl_clock (tl:tl_verifiable_log) (i:tl_idx tl): timestamp =
  Valid?.clock (verify (tl_prefix tl (i + 1)))

let tl_verify (tl:thread_id_logS) (i:tl_idx tl): vtls =
  verify (tl_prefix tl (i + 1))

(* Utilities for running all verifier threads and comparing aggregate add/evict hashes.
   Follows the definitions in Veritas.Verifier.Global. *) 

let gl_verifiable (gl: g_logS) = 
  forall (tid:seq_index gl). tl_verifiable (thread_log gl tid)

let gl_verifiable_log = gl:g_logS{gl_verifiable gl}

val lemma_gl_verifiable_implies_prefix_verifiable
  (gl:gl_verifiable_log) (i:nat{i <= Seq.length gl}):
  Lemma (ensures (gl_verifiable (prefix gl i)))
        [SMTPat (prefix gl i)]

let rec hadd_aux (gl: gl_verifiable_log)
  : Tot (ms_hash_value)
    (decreases (Seq.length gl)) 
  = let p = Seq.length gl in
    if p = 0 then empty_hash_value
    else
      let gl' = prefix gl (p - 1) in
      let h1 = hadd_aux gl' in
      let h2 = thread_hadd (verify (thread_log gl (p - 1))) in
      ms_hashfn_agg h1 h2

let hadd (gl: gl_verifiable_log): ms_hash_value = hadd_aux gl

let rec hevict_aux (gl: gl_verifiable_log)
  : Tot (ms_hash_value)
    (decreases (Seq.length gl))
  = let p = Seq.length gl in
    if p = 0 then empty_hash_value
    else
      let gl' = prefix gl (p - 1) in
      let h1 = hevict_aux gl' in
      let h2 = thread_hevict (verify (thread_log gl (p - 1))) in
      ms_hashfn_agg h1 h2

let hevict (gl: gl_verifiable_log): ms_hash_value = hevict_aux gl

let gl_hash_verifiable (gl: gl_verifiable_log): bool = 
  hadd gl = hevict gl

let gl_hash_verifiable_log = gl:gl_verifiable_log{gl_hash_verifiable gl}

let gl_clock (gl:gl_verifiable_log) (i:I.sseq_index gl): timestamp = 
  let (tid, idx) = i in  
  let tl = thread_log gl tid in
  tl_clock tl idx

let gl_verify (gl:g_logS) (i:I.sseq_index gl): vtls =
  let (tid, idx) = i in  
  let tl = thread_log gl tid in
  tl_verify tl idx

(* Utilities for verifying the global, interleaved log shared among all threads.
   Follows the definitions in Veritas.Verifier.TSLog. *) 

let il_verifiable (il: il_logS) = 
  gl_verifiable (g_logS_of il)

let il_clock (il: il_logS{il_verifiable il}) (i: I.seq_index il): timestamp =
  let gl = g_logS_of il in
  let j = I.i2s_map il i in
  gl_clock gl j

(* state at thread j after processing log entry i (which modifies the state of j) *)
let il_verify (il: il_logS) (i: I.seq_index il): vtls =
  let gl = g_logS_of il in
  let j = I.i2s_map il i in
  gl_verify gl j

val clock_sorted (il: il_logS {il_verifiable il}): prop
 
let its_log = il:il_logS{il_verifiable il /\ clock_sorted il}

let il_hash_verifiable (itsl: its_log) = gl_hash_verifiable (g_logS_of itsl)

let il_hash_verifiable_log = itsl:its_log {il_hash_verifiable itsl}

val lemma_prefix_verifiable (itsl: its_log) (i:nat{i <= I.length itsl}):
  Lemma (ensures (il_verifiable (I.prefix itsl i) /\ clock_sorted (I.prefix itsl i)))
        [SMTPat (I.prefix itsl i)]

// final correctness property
val lemma_verifier_correct (gl: gl_hash_verifiable_log { ~ (seq_consistent (to_state_op_glogS gl))})
  : hash_collision_gen 
