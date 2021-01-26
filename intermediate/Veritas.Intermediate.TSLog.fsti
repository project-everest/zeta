module Veritas.Intermediate.TSLog

open Veritas.Interleave
open Veritas.MultiSetHash
open Veritas.SeqAux
open Veritas.State
open Veritas.Verifier
open Veritas.Intermediate.Global
open Veritas.Intermediate.Logs
open Veritas.Intermediate.Store
open Veritas.Intermediate.Verify

module I = Veritas.Interleave
module SA = Veritas.SeqAux
module SpecTS = Veritas.Verifier.TSLog
module IntL = Veritas.Intermediate.Logs
module IntG = Veritas.Intermediate.Global
module IntT = Veritas.Intermediate.Thread
module IntV = Veritas.Intermediate.Verify

let il_logS vcfg = interleaving (logS_entry vcfg)

let thread_count #vcfg (il:il_logS vcfg) = Seq.length (s_seq il)

let valid_tid #vcfg (il:il_logS vcfg) = tid:nat{tid < thread_count il}

let g_logS_of #vcfg (il:il_logS vcfg): g_logS _ = s_seq il

let to_state_ops #vcfg (itsl:il_logS vcfg): Seq.seq (state_op) =
  IntL.to_state_ops (i_seq itsl)

let verifiable #vcfg (il: il_logS vcfg) = 
  IntG.verifiable (g_logS_of il)

/// the clock of an entry in a verifiable idx seq
let clock #vcfg (il: il_logS vcfg{verifiable il}) (i: I.seq_index il): timestamp =
  let gl = g_logS_of il in
  let j = i2s_map il i in
  IntG.clock gl j

val clock_sorted (#vcfg:_) (il: il_logS vcfg {verifiable il}): prop

let its_log vcfg = il:il_logS vcfg{verifiable il /\ clock_sorted il}

val create (#vcfg:_) (gl: verifiable_log vcfg): (itsl:its_log vcfg{g_logS_of itsl == gl})

let hash_verifiable #vcfg (itsl: its_log vcfg) = IntG.hash_verifiable (g_logS_of itsl)

let hash_verifiable_log vcfg = itsl: its_log vcfg{hash_verifiable itsl}

val lemma_prefix_verifiable (#vcfg:_) (itsl: its_log vcfg) (i:nat{i <= I.length itsl}):
  Lemma (ensures (verifiable (I.prefix itsl i) /\ clock_sorted (I.prefix itsl i)))
        [SMTPat (I.prefix itsl i)]

let thread_id_of #vcfg (il: its_log vcfg) (i: I.seq_index il): valid_tid il =
  fst (I.i2s_map il i)

let thread_state #vcfg (il:its_log vcfg)
                 (tid:valid_tid il)
  : Tot (vs:vtls vcfg{Valid? vs}) = 
  let gs = g_logS_of il in
  let tl = IntG.thread_log gs tid in
  IntT.verify tl

let thread_state_pre #vcfg (il: its_log vcfg) (i: I.seq_index il): (vs:vtls vcfg{Valid? vs}) = 
  let tid = thread_id_of il i in
  thread_state (I.prefix il i) tid

let thread_state_post #vcfg (il: its_log vcfg) (i: I.seq_index il): (vs:vtls vcfg{Valid? vs}) = 
  let tid = thread_id_of il i in
  thread_state (I.prefix il (i + 1)) tid

val lemma_verifier_thread_state_extend (#vcfg:_) (ils: its_log vcfg) (i: I.seq_index ils):
  Lemma (ensures (thread_state_post ils i == IntV.verify_step (thread_state_pre ils i) (I.index ils i)))
        [SMTPat (I.prefix ils i)]

val lemma_slot_is_merkle_points_to (#vcfg:_) (ils: its_log vcfg) (i: I.seq_index ils):
  Lemma (ensures (slot_points_to_is_merkle_points_to (IntV.thread_store (thread_state_pre ils i))))
        [SMTPat (I.prefix ils i)]

let lemma_logS_interleave_implies_state_ops_interleave #vcfg (l: logS vcfg) (gl: g_logS vcfg{interleave #(logS_entry vcfg) l gl})
  : Lemma (interleave #state_op (IntL.to_state_ops l) (IntG.to_state_ops gl)) 
  = FStar.Squash.bind_squash
      #(interleave l gl)
      #(interleave (IntL.to_state_ops l) (IntG.to_state_ops gl))
      ()
      (fun i -> 
        let i' = filter_map_interleaving is_state_op to_state_op i in
        FStar.Squash.return_squash i')

let same_shape #a #b (il:I.interleaving a) (il':I.interleaving b) =
  let open I in
  let IL s ss _ = il in
  let IL s' ss' _ = il' in
  Seq.length s == Seq.length s' /\
  Seq.length ss == Seq.length ss' /\
  (forall (i:SA.seq_index ss). Seq.length (Seq.index ss i) == Seq.length (Seq.index ss i))

val to_logk (#vcfg:_) (il:its_log vcfg) 
  : Tot (sil:SpecTS.il_vlog { same_shape il sil })

val lemma_to_logk_length (#vcfg:_) (il:its_log vcfg)
  : Lemma (ensures I.length il = I.length (to_logk il))
          [SMTPat (to_logk il)]

val lemma_to_logk_thread_count (#vcfg:_) (il:its_log vcfg)
  : Lemma (ensures thread_count il = SpecTS.thread_count (to_logk il))
          [SMTPat (to_logk il)]

val lemma_to_logk_thread_id_of (#vcfg:_) (il:its_log vcfg) (i:I.seq_index il)
  : Lemma (ensures thread_id_of il i == SpecTS.thread_id_of (to_logk il) i)
          [SMTPat (thread_id_of il i)]

val lemma_to_logk_prefix_commute (#vcfg:_) (il:its_log vcfg) (i:nat{i <= I.length il})
  : Lemma (to_logk (I.prefix il i) == I.prefix (to_logk il) i)
          [SMTPat (I.prefix il i)]

val lemma_to_logk_state_ops (#vcfg:_) (ils:its_log vcfg)
  : Lemma (ensures (let ilk = to_logk ils in
                    to_state_ops ils = SpecTS.state_ops ilk))
          [SMTPat (to_logk ils)]

val lemma_its_log_valid_step (#vcfg:_) (il:its_log vcfg) (i:I.seq_index il)
  : Lemma (ensures Valid? (IntV.verify_step (thread_state_pre il i) (I.index il i)))
          [SMTPat (thread_state_pre il i)]

val lemma_valid_logs_entry (#vcfg:_) (il: its_log vcfg) (i:I.seq_index il)
  : Lemma (ensures (IntV.valid_logS_entry (thread_state_pre il i) (I.index il i)))
          [SMTPat (I.index il i)]

let to_logK_entry #vcfg (il:its_log vcfg) (i:I.seq_index il) = 
  IntV.to_logK_entry (thread_state_pre il i) (I.index il i)

val lemma_to_logk_index (#vcfg:_) (ils:its_log vcfg) (i:I.seq_index ils)
  : Lemma (ensures (I.index (to_logk ils) i == to_logK_entry ils i))
          [SMTPat (I.index ils i)]
            
(* after processing il, the thread store of every verifier thread is a map *)
let forall_store_ismap #vcfg (il:its_log vcfg)
  = forall (tid:valid_tid il). 
    {:pattern (thread_store (thread_state il tid))}
      is_map (thread_store (thread_state il tid))

(* 
 * if all the stores are maps before entry i and the store after processing entry i step is a map, then 
 * all stores are maps after entry i 
 *)
val lemma_forall_store_ismap_extend (#vcfg:_) (il:its_log vcfg) (i:I.seq_index il)
  : Lemma (requires (forall_store_ismap (I.prefix il i) /\ 
                     is_map (thread_store (thread_state_post il i))))
          (ensures (forall_store_ismap (I.prefix il (i + 1))))

(* 
 * the property that for an its_log ils, ils and (to_logk ils) are vts_rel 
 * for every thread 
 *)
let forall_vtls_rel #vcfg (ils:its_log vcfg)
  = let ilk = to_logk ils in    
    (forall (tid:valid_tid ils). 
      {:pattern vtls_rel (thread_state ils tid) (SpecTS.thread_state ilk tid)}
       vtls_rel (thread_state ils tid) (SpecTS.thread_state ilk tid))

val lemma_forall_vtls_rel_extend (#vcfg:_) (ils:its_log vcfg) (i:I.seq_index ils)
  : Lemma (requires (let ils_i = I.prefix ils i in
                     let ilk = to_logk ils in
                     let ilk_i = I.prefix ilk i in                     
                     forall_vtls_rel ils_i /\
                     vtls_rel (thread_state_post ils i) 
                              (SpecTS.thread_state_post ilk i)))
          (ensures (let ilk = to_logk ils in
                    let ils_i1 = I.prefix ils (i + 1) in
                    forall_vtls_rel ils_i1))

val lemma_forall_vtls_rel_implies_spec_verifiable (#vcfg:_) (ils:its_log vcfg)
  : Lemma (requires (forall_vtls_rel ils))
          (ensures (let ilk = to_logk ils in
                    SpecTS.verifiable ilk))
          [SMTPat (forall_vtls_rel ils)]

val lemma_vtls_rel_implies_spec_clock_sorted (#vcfg:_) (ils:its_log vcfg)
  : Lemma (requires (forall_vtls_rel ils))
          (ensures (let ilk = to_logk ils  in
                    SpecTS.clock_sorted ilk))
          [SMTPat (forall_vtls_rel ils)]

val lemma_vtls_rel_implies_hash_verifiable (#vcfg:_) (ils:hash_verifiable_log vcfg)
  : Lemma (requires (forall_vtls_rel ils))
          (ensures (let ilk = to_logk ils in
                    SpecTS.hash_verifiable ilk))
          [SMTPat (forall_vtls_rel ils)]

let spec_rel #vcfg (ils: its_log vcfg) = 
  forall_store_ismap ils /\
  forall_vtls_rel ils

val lemma_empty_implies_spec_rel (#vcfg:_) (ils:its_log vcfg{I.length ils = 0})
  : Lemma (spec_rel ils)

val lemma_spec_rel_implies_prefix_spec_rel (#vcfg:_) (ils:its_log vcfg) (i:nat{i <= I.length ils})
 : Lemma (ensures (let ils' = I.prefix ils i in
                   spec_rel ils'))

///  If the i'th position in the interleaved log is an evict to blum (EvictB/EvictBM) return the
///  multiset element at this position (that is added to the evict set)
/// 
let blum_evict_elem #vcfg (ils: its_log vcfg) 
                          (i:I.seq_index ils{is_evict_to_blum (I.index ils i)}): ms_hashfn_dom =
  let gl = g_logS_of ils in
  let ii = i2s_map ils i in
  IntG.blum_evict_elem gl ii

///  Some properties of the blum evict element returned at the position i
///
val lemma_blum_evict_def (#vcfg:_) 
                         (ils: its_log vcfg) 
                         (i:I.seq_index ils {is_evict_to_blum (I.index ils i)})
  : Lemma (ensures (let be = blum_evict_elem ils i in
                    let tid = thread_id_of ils i in
                    let vs = thread_state_pre ils i in
                    let st = IntV.thread_store vs in
                    let e = I.index ils i in
                    let s = slot_of e in
                    inuse_slot st s /\
                    (let k = stored_key st s in
                     let v = stored_value st s in
                     match e with
                     | EvictB_S _ t -> be = MHDom (k,v) t tid
                     | EvictBM_S _ _ t -> be = MHDom (k,v) t tid
                    )))
                         
val lemma_clock_ordering (#vcfg:_) (itsl: its_log vcfg) (i1 i2: I.seq_index itsl):
  Lemma (requires (clock itsl i1 `ts_lt` clock itsl i2))
        (ensures (i1 < i2))
