module Veritas.Intermediate.TSLog
open FStar.Calc
module VG = Veritas.Intermediate.Global
module VT = Veritas.Intermediate.Thread

#push-options "--query_stats --max_fuel 0 --max_ifuel 0 --z3rlimit_factor 4"
let lemma_prefix_clock_sorted #vcfg 
                              (itsl: its_log vcfg) 
                              (i:nat{i <= I.length itsl})
  : Lemma
    (requires
      verifiable (I.prefix itsl i))
    (ensures
      clock_sorted (I.prefix itsl i))
  = assert (clock_sorted itsl);
    let itsl' = I.prefix itsl i in
    let aux (t0 t1:I.seq_index itsl')
      : Lemma (requires t0 <= t1)
              (ensures clock itsl' t0 `ts_leq` clock itsl' t1)
              [SMTPat(clock itsl' t0 `ts_leq` clock itsl' t1)]
      = assert (clock itsl t0 `ts_leq` clock itsl t1);
        lemma_i2s_map_prefix itsl i t0;
        lemma_i2s_map_prefix itsl i t1;
        I.lemma_prefix_index itsl i t0;
        I.lemma_prefix_index itsl i t1;
        I.per_thread_prefix itsl i;
        calc (==) {
         clock itsl' t0;
          == {}
         clock (I.prefix itsl i) t0;
          == {}
         VG.clock (g_logS_of itsl') (i2s_map itsl' t0);
          == {}
         VG.clock (g_logS_of itsl') (i2s_map itsl t0);
        }
    in
    ()

let lemma_prefix_verifiable #vcfg (itsl: its_log vcfg) (i:nat{i <= I.length itsl})
  : Lemma
    (ensures
      verifiable (I.prefix itsl i) /\
      clock_sorted (I.prefix itsl i))
  = assert (verifiable itsl);
    assert (clock_sorted itsl);
    let ss = g_logS_of itsl in
    let itsl' = I.prefix itsl i in
    let ss' = g_logS_of itsl' in
    assert (Seq.length ss = Seq.length ss');
    let aux (tid:SA.seq_index ss)
      : Lemma (VT.verifiable (thread_log ss' tid))
              [SMTPat (thread_log ss' tid)]
      = let tl = thread_log ss tid in
        assert (VT.verifiable tl);
        I.per_thread_prefix itsl i;
        let tl' = thread_log ss' tid in
        VT.verifiable_implies_prefix_verifiable tl (Seq.length (snd tl'))
    in
    lemma_prefix_clock_sorted itsl i

let create (#vcfg:_) (gl: verifiable_log vcfg)
  : itsl:its_log vcfg{g_logS_of itsl == gl}
  = admit()

#push-options "--max_fuel 1"
let lemma_verifier_thread_state_extend (#vcfg:_) (itsl: its_log vcfg) (i: I.seq_index itsl)
  : Lemma (ensures (thread_state_post itsl i ==
                    IntV.verify_step (thread_state_pre itsl i) (I.index itsl i))) 
  = let tid = thread_id_of itsl i in
    let itsl_i = I.prefix itsl i in
    let vlog_tid = Seq.index (s_seq itsl_i) tid in
    let itsl_i' = I.prefix itsl (i + 1) in
    let vlog_tid' = Seq.index (s_seq itsl_i') tid in
    I.lemma_prefix_snoc itsl i;
    assert (vlog_tid' `Seq.equal` Seq.snoc vlog_tid (I.index itsl i));
    assert (prefix vlog_tid' (Seq.length vlog_tid' - 1) `Seq.equal` vlog_tid);
    ()
#pop-options

let lemma_slot_is_merkle_points_to (#vcfg:_) (ils: its_log vcfg) (i: I.seq_index ils)
  : Lemma (ensures (slot_points_to_is_merkle_points_to (IntV.thread_store (thread_state_pre ils i))))
  = admit()

#push-options "--max_fuel 2 --max_ifuel 1 --z3rlimit_factor 4"
let int_add_sub_log #vcfg (il:its_log vcfg { IntAdd? (IL?.prf il) })
  : its_log vcfg
  = let IL s ss prf = il in
    let IntAdd s' ss' prf' = prf in
    let il' = IL s' ss' prf' in
    assert(Seq.equal ss (append1 ss' Seq.empty));
    assert (forall (tid:Veritas.SeqAux.seq_index ss'). IntG.thread_log ss' tid == IntG.thread_log ss tid);
    I.i2s_map_int_add il';
    assert (forall (i:I.seq_index il'). clock il' i == clock il i);      
    assert (clock_sorted il');      
    il'

let int_extend_sub_log #vcfg (il:its_log vcfg { IntExtend? (IL?.prf il) })
  : il':its_log vcfg{il' == I.prefix il (I.length il - 1)} 
  = let IL s ss prf = il in
    let IntExtend s0 ss0 prf x i = prf in
    let il' = IL _ _ prf in
    I.hprefix_extend _ _ prf x i;      
    let n' = I.length il - 1 in
    lemma_prefix_verifiable il' n';
    assert(il' == I.prefix il n');
    il'

let int_extend_logK_entry #vcfg (il:its_log vcfg { IntExtend? (IL?.prf il) })
  : logK_entry
  = let IL s ss prf = il in
    let IntExtend s0 ss0 prf x i = prf in
    let n' = I.length il - 1 in
    let vss_pre = thread_state_pre il n' in
    assert (I.index il n' == x);
    let ek = IntV.to_logK_entry vss_pre x in
    ek

let rec to_logk_aux #vcfg (il:its_log vcfg) 
  : Tot (sil:SpecTS.il_vlog { same_shape il sil })
        (decreases (I.IL?.prf il))
  = let IL s ss prf = il in
    match prf with
    | IntEmpty -> 
      IL _ _ IntEmpty

    | IntAdd s' ss' prf ->
      let il' = int_add_sub_log il in
      let IL _ _ prf = to_logk_aux il' in
      let res = IL _ _ (IntAdd _ _ prf) in
      res      

    | IntExtend s0 ss0 prf x i ->
      let n' = I.length il - 1 in
      let il' = int_extend_sub_log il in
      let ek = int_extend_logK_entry il in
      let IL _ ss0k prfk = to_logk_aux il' in 
      let res = I.IntExtend _ _ prfk ek i in
      IL _ _ res      
#pop-options

let to_logk (#vcfg:_) (il:its_log vcfg) 
  : Tot (sil:SpecTS.il_vlog { same_shape il sil }) = 
  to_logk_aux il

let lemma_to_logk_length (#vcfg:_) (il:its_log vcfg)
  : Lemma (ensures I.length il = I.length (to_logk il)) = ()

let lemma_to_logk_thread_count (#vcfg:_) (il:its_log vcfg)
  : Lemma (ensures thread_count il = SpecTS.thread_count (to_logk il))
  = ()

#push-options "--ifuel 1,1 --fuel 1,1"

let lemma_to_logk_prefix_commute_aux (#vcfg:_) (il:its_log vcfg) (i:nat{i <= I.length il})
  : Lemma (to_logk (I.prefix il i) == I.prefix (to_logk il) i)
  = admit()

let rec lemma_to_logk_thread_id_of_aux (#vcfg:_) (il:its_log vcfg) (i:I.seq_index il)
  : Lemma (ensures thread_id_of il i == SpecTS.thread_id_of (to_logk il) i)
          (decreases IL?.prf il)
  = let IL s ss prf = il in
    match prf with
    | IntEmpty -> ()

    | IntAdd s' ss' prf' ->
      let il' = int_add_sub_log il in
      lemma_to_logk_thread_id_of_aux il' i; 
      I.i2s_map_int_add il';
      I.i2s_map_int_add (to_logk il');
      assert (thread_id_of il' i == thread_id_of il i);
      assert (SpecTS.thread_id_of (to_logk il) i == SpecTS.thread_id_of (to_logk il') i)

    | IntExtend s0 ss0 prf x j ->
      let il' = int_extend_sub_log il in
      if i = I.length il - 1 
      then (
        i2s_map_int_extend _ _ prf x j i;
        assert (thread_id_of il i == j);
        let lk' = to_logk il' in
        let lk = to_logk il in
        i2s_map_int_extend _ _ (IL?.prf lk') (int_extend_logK_entry il) j i
      )
      else (
        lemma_to_logk_thread_id_of_aux il' i;
        lemma_to_logk_prefix_commute_aux il (I.length il - 1);
        I.lemma_i2s_map_prefix il (I.length il - 1) i;
        I.lemma_i2s_map_prefix (to_logk il) (I.length il - 1) i
      )

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
                         
let lemma_clock_ordering (#vcfg:_) (itsl: its_log vcfg) (i1 i2: I.seq_index itsl):
  Lemma (requires (clock itsl i1 `ts_lt` clock itsl i2))
        (ensures (i1 < i2)) = admit()
