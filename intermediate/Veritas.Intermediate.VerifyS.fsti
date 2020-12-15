module Veritas.Intermediate.VerifyS

open Veritas.Intermediate.Logs
open Veritas.Intermediate.StoreS

(* These are all independent of the 'verify' function; they should be safe to open *)
open Veritas.BinTree
open Veritas.Hash
open Veritas.Key
open Veritas.MultiSetHash
open Veritas.MultiSetHashDomain
open Veritas.Record
open Veritas.SeqAux

(* It's better not to open these modules to avoid naming conflicts *)
module I = Veritas.Interleave
module Spec = Veritas.Verifier
module SpecVT = Veritas.Verifier.Thread
module SpecVG = Veritas.Verifier.Global
module SpecVTS = Veritas.Verifier.TSLog
module SpecVC = Veritas.Verifier.Correctness

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

let thread_store_size (vs: vtls {Valid? vs}): nat =
  let st = thread_store vs in Seq.length st

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

let vget (s:slot_id) (k:key) (v:data_value) (vs: vtls {Valid? vs}) : vtls =
  let st = thread_store vs in
  (* check store contains slot s *)
  if not (store_contains st s) then Failed
  (* check stored key and value *)
  else let k' = stored_key st s in
       let v' = stored_value st s in
       if k <> k' then Failed
       else if not (DVal? v') then Failed
       else if to_data_value v' <> v then Failed
       else vs

let vput (s:slot_id) (k:key) (v:data_value) (vs: vtls {Valid? vs}) : vtls =
  let st = thread_store vs in
  (* check store contains slot s *)
  if not (store_contains st s) then Failed
  (* check stored key is k *)
  else let k' = stored_key st s in
       if k <> k' then Failed
       else if not (is_data_key (stored_key st s)) then Failed
       else update_thread_store vs (update_value st s (DVal v))

let vaddm (s:slot_id) (r:record) (s':slot_id) (vs: vtls {Valid? vs}): vtls =
  if not (s < thread_store_size vs) then Failed
  else 
    let st = thread_store vs in
    let (k,v) = r in
    (* check store contains slot s' *)
    if not (store_contains st s') then Failed
    else
      let k' = stored_key st s' in
      let v' = stored_value st s' in
      (* check k is a proper desc of k' *)
      if not (is_proper_desc k k') then Failed
      (* check store does not contain slot s *)
      else if store_contains st s then Failed
      (* check type of v is consistent with k *)
      else if not (is_value_of k v) then Failed
      (* check v' is a merkle value *)
      else if DVal? v' then Failed 
      else
        let v' = to_merkle_value v' in
        let d = desc_dir k k' in
        let dh' = desc_hash_dir v' d in 
        let h = hashfn v in
        match dh' with
        | Empty -> (* k' has no child in direction d *)
            (* first add must be init value *)
            if v <> init_value k then Failed
            else
              let v'_upd = Spec.update_merkle_value v' d k h false in
              let st_upd = update_value st s' (MVal v'_upd) in
              let st_upd2 = add_to_store st_upd s k v Spec.MAdd in
              let st_upd3 = update_in_store st_upd2 s' d true in
              update_thread_store vs st_upd3
        | Desc k2 h2 b2 -> 
            if k2 = k 
            then (* k is a child of k' *)
              (* check hashes match and k was not evicted to blum *)
              if not (h2 = h && b2 = false) then Failed
              (* check store does not contain k *)
              else if in_store_bit st s' d then Failed
              else 
                let st_upd = add_to_store st s k v Spec.MAdd in
                let st_upd2 = update_in_store st_upd s' d true in
                update_thread_store vs st_upd2
            else (* otherwise, k is not a child of k' *)
            (* first add must be init value *)
            if v <> init_value k then Failed
            (* check k2 is a proper desc of k *)
            else if not (is_proper_desc k2 k) then Failed
            else
              let d2 = desc_dir k2 k in
              let inb = in_store_bit st s' d in // original in_store bit for s' in direction d
              let mv = to_merkle_value v in
              let mv_upd = Spec.update_merkle_value mv d2 k2 h2 b2 in
              let v'_upd = Spec.update_merkle_value v' d k h false in
              let st_upd = update_value st s' (MVal v'_upd) in
              let st_upd2 = add_to_store st_upd s k (MVal mv_upd) Spec.MAdd in
              let st_upd3 = update_in_store st_upd2 s' d true in
              let st_upd4 = update_in_store st_upd3 s d2 inb in
              update_thread_store vs st_upd4

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

let vevictb (s:slot_id) (t:timestamp) (vs:vtls {Valid? vs}): vtls = 
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
    else if add_method_of st s <> Spec.BAdd then Failed
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
            vevictb s t (update_thread_store vs st_upd2)

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

(* convert slot-based log entry e to a key-based log entry, given verifier state vtls *)
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

val lemma_init_thread_state_rel (id:thread_id) :
  Lemma (vtls_rel (init_thread_state id) (Spec.init_thread_state id))

val lemma_t_verify_simulates_spec (id:thread_id) (l:logS) 
  : Lemma (requires (Valid? (t_verify id l)))
          (ensures (vtls_rel (t_verify id l) (Spec.t_verify id (logS_to_logK id l))))

val lemma_logS_to_logK_to_state_op (id:thread_id) (l:logS{Valid? (t_verify id l)})
  : Lemma (ensures (Seq.equal (to_state_op_logS l) 
                              (Veritas.EAC.to_state_op_vlog (logS_to_logK id l))))
           [SMTPat (Veritas.EAC.to_state_op_vlog (logS_to_logK id l))]

(* Utilities for running a single verifier thread.
   Follows the definitions in Veritas.Verifier.Thread. *)

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

let tl_logS_to_logK (tl:tl_verifiable_log{is_map (thread_store (verify tl))}) 
  : SpecVT.verifiable_log
  = lemma_t_verify_simulates_spec (fst tl) (snd tl);
    (fst tl, logS_to_logK (fst tl) (snd tl))

let lemma_tl_length (tl:tl_verifiable_log{is_map (thread_store (verify tl))})
  : Lemma (ensures tl_length tl = SpecVT.length (tl_logS_to_logK tl))
          [SMTPat (tl_length tl)]
  = admit()

// may be useful
let lemma_tl_clock_simulates_spec (tl: tl_verifiable_log{is_map (thread_store (verify tl))}) (i:tl_idx tl)
  : Lemma (tl_clock tl i = SpecVT.clock (tl_logS_to_logK tl) i)
  = admit()

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

let forall_is_map (gl:gl_verifiable_log)
  = forall (tid:seq_index gl). is_map (thread_store (verify (thread_log gl tid)))

val glogS_to_logK (gl:gl_verifiable_log{forall_is_map gl}) 
  : gl':SpecVG.verifiable_log{Seq.length gl = Seq.length gl'}

val lemma_glogS_to_logK (gl:gl_verifiable_log{forall_is_map gl}) (id:seq_index gl)
  : Lemma (ensures Seq.index (glogS_to_logK gl) id = logS_to_logK id (Seq.index gl id))
          [SMTPat (Seq.index (glogS_to_logK gl) id)]

val lemma_hadd_equal (gl:gl_verifiable_log{forall_is_map gl}) 
  : Lemma (hadd gl = SpecVG.hadd (glogS_to_logK gl))

val lemma_hevict_equal (gl:gl_verifiable_log{forall_is_map gl}) 
  : Lemma (hevict gl = SpecVG.hevict (glogS_to_logK gl))

let lemma_gl_hash_verifiable_simulates_spec (gl:gl_hash_verifiable_log{forall_is_map gl})
  : Lemma (SpecVG.hash_verifiable (glogS_to_logK gl))
  = lemma_hadd_equal gl;
    lemma_hevict_equal gl

let lemma_to_state_op_glogS (gl: gl_verifiable_log{forall_is_map gl})
  : Lemma (ensures (Seq.equal (to_state_op_glogS gl) 
                              (SpecVC.to_state_op_gvlog (glogS_to_logK gl))))
  = let aux (i:seq_index gl) 
      : Lemma (Seq.index (to_state_op_glogS gl) i = 
              Seq.index (SpecVC.to_state_op_gvlog (glogS_to_logK gl)) i)
      = () in
    Classical.forall_intro aux

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

val il_create (gl: gl_verifiable_log): (itsl:its_log{g_logS_of itsl == gl})

