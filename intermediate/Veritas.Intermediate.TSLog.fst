module Veritas.Intermediate.TSLog

let clock_sorted (#vcfg:_) (il: il_logS vcfg {verifiable il}): prop = admit()

let create (#vcfg:_) (gl: verifiable_log vcfg): (itsl:its_log vcfg{g_logS_of itsl == gl}) = admit()

let lemma_prefix_verifiable (#vcfg:_) (itsl: its_log vcfg) (i:nat{i <= I.length itsl}):
  Lemma (ensures (verifiable (I.prefix itsl i) /\ clock_sorted (I.prefix itsl i))) = admit()

let lemma_verifier_thread_state_extend (#vcfg:_) (ils: its_log vcfg) (i: I.seq_index ils):
  Lemma (ensures (thread_state_post ils i == IntV.verify_step (thread_state_pre ils i) (I.index ils i))) = admit()

let lemma_slot_is_merkle_points_to (#vcfg:_) (ils: its_log vcfg) (i: I.seq_index ils):
  Lemma (ensures (slot_points_to_is_merkle_points_to (IntV.thread_store (thread_state_pre ils i)))) = admit()

let to_logk (#vcfg:_) (il:its_log vcfg) 
  : Tot (sil:SpecTS.il_vlog { same_shape il sil }) = admit()

let lemma_to_logk_length (#vcfg:_) (il:its_log vcfg)
  : Lemma (ensures I.length il = I.length (to_logk il)) = admit()

let lemma_to_logk_thread_count (#vcfg:_) (il:its_log vcfg)
  : Lemma (ensures thread_count il = SpecTS.thread_count (to_logk il))
  = admit()

let lemma_to_logk_thread_id_of (#vcfg:_) (il:its_log vcfg) (i:I.seq_index il)
  : Lemma (ensures thread_id_of il i == SpecTS.thread_id_of (to_logk il) i)
  = admit()

let lemma_to_logk_prefix_commute (#vcfg:_) (il:its_log vcfg) (i:nat{i <= I.length il})
  : Lemma (to_logk (I.prefix il i) == I.prefix (to_logk il) i)
  = admit()

let lemma_to_logk_state_ops (#vcfg:_) (ils:its_log vcfg)
  : Lemma (ensures (let ilk = to_logk ils in
                    to_state_ops ils = SpecTS.state_ops ilk))
  = admit()

let lemma_its_log_valid_step (#vcfg:_) (il:its_log vcfg) (i:I.seq_index il)
  : Lemma (ensures Valid? (IntV.verify_step (thread_state_pre il i) (I.index il i)))
  = admit()

let lemma_valid_logs_entry (#vcfg:_) (il: its_log vcfg) (i:I.seq_index il)
  : Lemma (ensures (IntV.valid_logS_entry (thread_state_pre il i) (I.index il i)))
  = admit()

let lemma_to_logk_index (#vcfg:_) (ils:its_log vcfg) (i:I.seq_index ils)
  : Lemma (ensures (I.index (to_logk ils) i == to_logK_entry ils i))
  = admit()

let lemma_forall_store_ismap_extend (#vcfg:_) (il:its_log vcfg) (i:I.seq_index il)
  : Lemma (requires (forall_store_ismap (I.prefix il i) /\ 
                     is_map (thread_store (thread_state_post il i))))
          (ensures (forall_store_ismap (I.prefix il (i + 1)))) = admit()

let lemma_forall_vtls_rel_extend (#vcfg:_) (ils:its_log vcfg) (i:I.seq_index ils)
  : Lemma (requires (let ils_i = I.prefix ils i in
                     let ilk = to_logk ils in
                     let ilk_i = I.prefix ilk i in                     
                     forall_vtls_rel ils_i /\
                     vtls_rel (thread_state_post ils i) 
                              (SpecTS.thread_state_post ilk i)))
          (ensures (let ilk = to_logk ils in
                    let ils_i1 = I.prefix ils (i + 1) in
                    forall_vtls_rel ils_i1)) = admit()

let lemma_forall_vtls_rel_implies_spec_verifiable (#vcfg:_) (ils:its_log vcfg)
  : Lemma (requires (forall_vtls_rel ils))
          (ensures (let ilk = to_logk ils in
                    SpecTS.verifiable ilk))
  = admit()

let lemma_vtls_rel_implies_spec_clock_sorted (#vcfg:_) (ils:its_log vcfg)
  : Lemma (requires (forall_vtls_rel ils))
          (ensures (let ilk = to_logk ils  in
                    SpecTS.clock_sorted ilk))
  = admit()

let lemma_vtls_rel_implies_hash_verifiable (#vcfg:_) (ils:hash_verifiable_log vcfg)
  : Lemma (requires (forall_vtls_rel ils))
          (ensures (let ilk = to_logk ils in
                    SpecTS.hash_verifiable ilk))
  = admit()

let lemma_empty_implies_spec_rel (#vcfg:_) (ils:its_log vcfg{I.length ils = 0})
  : Lemma (spec_rel ils) = admit()

let lemma_spec_rel_implies_prefix_spec_rel (#vcfg:_) (ils:its_log vcfg) (i:nat{i <= I.length ils})
 : Lemma (ensures (let ils' = I.prefix ils i in
                   spec_rel ils')) = admit()

let lemma_blum_evict_def (#vcfg:_) 
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
                    ))) = admit()
                         
