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

let rec to_logk #vcfg (il:its_log vcfg) 
  : Tot (sil:SpecTS.il_vlog { same_shape il sil })
        (decreases (I.IL?.prf il))
  = let IL s ss prf = il in
    match prf with
    | IntEmpty -> 
      IL _ _ IntEmpty

    | IntAdd s' ss' prf ->
      let il' = int_add_sub_log il in
      let IL _ _ prf = to_logk il' in
      let res = IL _ _ (IntAdd _ _ prf) in
      res      

    | IntExtend s0 ss0 prf x i ->
      let n' = I.length il - 1 in
      let il' = int_extend_sub_log il in
      let ek = int_extend_logK_entry il in
      let IL _ ss0k prfk = to_logk il' in 
      let res = I.IntExtend _ _ prfk ek i in
      IL _ _ res      
#pop-options

let lemma_to_logk_length (#vcfg:_) (il:its_log vcfg)
  : Lemma (ensures I.length il = I.length (to_logk il)) = ()

let lemma_to_logk_thread_count (#vcfg:_) (il:its_log vcfg)
  : Lemma (ensures thread_count il = SpecTS.thread_count (to_logk il))
  = ()

#push-options "--ifuel 1,1 --fuel 1,1"
let rec lemma_to_logk_prefix_commute (#vcfg:_) (il:its_log vcfg) (i:nat{i <= I.length il})
  : Lemma 
    (ensures to_logk (I.prefix il i) == I.prefix (to_logk il) i)
    (decreases (IL?.prf il))
  =  let IL s ss prf = il in
     match prf with
     | IntEmpty -> 
        I.prefix_identity il;
        I.prefix_identity (to_logk il)

     | IntAdd _ _ prf' ->
        let il' = int_add_sub_log il in
        calc 
        (==) {
          to_logk (I.prefix il i);
        (==){ I.prefix_int_add il i }
          IL _ _ (IntAdd _ _ (IL?.prf (to_logk (I.prefix il' i))));
        (==){ lemma_to_logk_prefix_commute il' i }
          IL _ _ (IntAdd _ _ (IL?.prf (I.prefix (to_logk il') i)));
        (==){ I.prefix_int_add (to_logk il) i }
          I.prefix (to_logk il) i;
        }
        
     | IntExtend s' ss' prf' x j ->
        I.prefix_int_extend il i;
        lemma_to_logk_length il;
        if i <= Seq.length s'
        then (
          let il' = int_extend_sub_log il in
          lemma_to_logk_prefix_commute il' i;
          assert (to_logk (I.prefix il' i) == I.prefix (to_logk il') i);
          assert (I.prefix il i == I.prefix il' i);
          I.prefix_int_extend (to_logk il) i
        )
        else (
          calc 
          (==) {
            to_logk (I.prefix il i);
          (==) {}
            to_logk il;
          (==) { lemma_to_logk_length il;
                 I.prefix_identity (to_logk il) }
            I.prefix (to_logk il) i;
          }
        )

let rec lemma_to_logk_thread_id_of (#vcfg:_) (il:its_log vcfg) (i:I.seq_index il)
  : Lemma (ensures thread_id_of il i == SpecTS.thread_id_of (to_logk il) i)
          (decreases IL?.prf il)
  = let IL s ss prf = il in
    match prf with
    | IntEmpty -> ()

    | IntAdd s' ss' prf' ->
      let il' = int_add_sub_log il in
      lemma_to_logk_thread_id_of il' i; 
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
        lemma_to_logk_thread_id_of il' i;
        lemma_to_logk_prefix_commute il (I.length il - 1);
        I.lemma_i2s_map_prefix il (I.length il - 1) i;
        I.lemma_i2s_map_prefix (to_logk il) (I.length il - 1) i
      )

let rec lemma_to_logk_state_ops (#vcfg:_) (il:its_log vcfg)
  : Lemma (ensures (to_state_ops il == SpecTS.state_ops (to_logk il)))
          (decreases (IL?.prf il))
  = let IL s ss prf = il in
    match prf with
    | IntEmpty -> 
      filter_map_emp (is_state_op #vcfg) (to_state_op #vcfg);
      filter_map_emp (Veritas.EAC.is_state_op) (Veritas.EAC.to_state_op)

    | IntAdd s' ss' prf' ->
      let il' = int_add_sub_log il in
      lemma_to_logk_state_ops il'

    | IntExtend s0 ss0 prf x j ->
      let il' = int_extend_sub_log il in
      lemma_to_logk_state_ops il';
      assert (I.i_seq il == Seq.snoc (I.i_seq il') x);
      filter_map_snoc (is_state_op #vcfg) (to_state_op #vcfg) (I.i_seq il') x;
      filter_map_snoc (Veritas.EAC.is_state_op) (Veritas.EAC.to_state_op) (I.i_seq (to_logk il')) (int_extend_logK_entry il)

let lemma_its_log_valid_step (#vcfg:_) (il:its_log vcfg) (i:I.seq_index il)
  : Lemma (ensures Valid? (IntV.verify_step (thread_state_pre il i) (I.index il i)))
  = ()

let lemma_valid_logs_entry (#vcfg:_) (il: its_log vcfg) (i:I.seq_index il)
  : Lemma (ensures (IntV.valid_logS_entry (thread_state_pre il i) (I.index il i)))
  = ()

let thread_state_int_add (#vcfg:_) (il:its_log vcfg{IntAdd? (IL?.prf il)}) (tid:valid_tid il { tid < Seq.length (I.s_seq il) - 1})
  : Lemma (thread_state il tid == thread_state (int_add_sub_log il) tid)
  = ()

let rec lemma_to_logk_last (#vcfg:_) (ils:its_log vcfg { I.length ils > 0 }) 
  : Lemma (ensures (I.index (to_logk ils) (I.length ils - 1) == to_logK_entry ils (I.length ils - 1)))
          (decreases (IL?.prf ils))
  = let n = I.length ils - 1 in
    let lhs = I.index (to_logk ils) n in
    let IL _ _ prf = ils in
    match prf with
    | IntEmpty -> ()
    | IntExtend _ _ prf' x j ->
      assert (lhs == int_extend_logK_entry ils)
    | IntAdd _ _ prf' -> 
      let ils' = int_add_sub_log ils in
      lemma_to_logk_last ils';
      I.prefix_int_add ils n;
      let tid = thread_id_of ils n in
      I.i2s_map_int_add ils';
      thread_state_int_add (I.prefix ils n) tid;      
      calc 
      (==) {
        I.index (to_logk ils) n;
      (==) {}
        I.index (to_logk ils') n;
      (==) { lemma_to_logk_last ils' }
        to_logK_entry ils' n;
      (==) { }
        IntV.to_logK_entry (thread_state_pre ils' n) (I.index ils' n);
      (==) { }        
        IntV.to_logK_entry (thread_state_pre ils' n) (I.index ils n);
      (==) {  calc 
              (==) {
                thread_state_pre ils' n;
              (==) { }
                thread_state (I.prefix ils' n) (thread_id_of ils' n);
              (==) { }
                thread_state (I.prefix ils' n) (thread_id_of ils n);              
              (==) { }
                thread_state (I.prefix ils n) (thread_id_of ils n); 
              (==) { }
                thread_state_pre ils n;
              }
           }
        IntV.to_logK_entry (thread_state_pre ils n) (I.index ils n);      
      (==) { }        
        to_logK_entry ils n;        
      }

module T = FStar.Tactics
#push-options "--fuel 0 --ifuel 0"
let lemma_to_logk_index (#vcfg:_) (ils:its_log vcfg) (i:I.seq_index ils)
  : Lemma (ensures (I.index (to_logk ils) i == to_logK_entry ils i))
  = calc 
    (==) {
     I.index (to_logk ils) i;
    (==) { I.lemma_prefix_index (to_logk ils) (i + 1) i}
     I.index (I.prefix (to_logk ils) (i + 1)) i;
    (==) { lemma_to_logk_prefix_commute ils (i + 1) }
     I.index (to_logk (I.prefix ils (i + 1))) i;
    };
    lemma_to_logk_last (I.prefix ils (i + 1));
    assert (I.index (to_logk (I.prefix ils (i + 1))) i ==
            to_logK_entry (I.prefix ils (i + 1)) i);
    let ils_i = I.prefix ils (i + 1) in   
    calc
    (==) {
      to_logK_entry ils_i i;
    (==) { }
      IntV.to_logK_entry (thread_state_pre ils_i i) (I.index ils_i i);
    (==) { I.lemma_prefix_index ils (i + 1) i }
      IntV.to_logK_entry (thread_state_pre ils_i i) (I.index ils i);
    (==) { 
             calc
             (==) {
               thread_state_pre ils_i i;
             (==) { 
                    I.lemma_i2s_map_prefix ils (i + 1) i; 
                    I.lemma_prefix_prefix ils (i + 1) i 
                  }
               thread_state_pre ils i;             
             }
         }
      IntV.to_logK_entry (thread_state_pre ils i) (I.index ils i);    
    }
#pop-options

#push-options "--fuel 0 --ifuel 0"
let lemma_thread_id_of_prefix (#vcfg:_) (il:its_log vcfg) (j:nat{ j <= I.length il}) (i:I.seq_index il { i < j })
  : Lemma (thread_id_of il i == thread_id_of (I.prefix il j) i)
  = I.lemma_i2s_map_prefix il j i

let lemma_thread_state_pre_prefix (#vcfg:_) (il:its_log vcfg) (j:nat{ j <= I.length il}) (i:I.seq_index il { i < j })
  : Lemma (thread_state_pre il i == thread_state_pre (I.prefix il j) i)
  = calc
    (==) {
       thread_state_pre il i;    
    (==) {}
      thread_state (I.prefix il i) (thread_id_of il i);
    (==) { I.lemma_prefix_prefix il j i }
      thread_state (I.prefix (I.prefix il j) i) (thread_id_of il i);    
    (==) { lemma_thread_id_of_prefix il j i }
      thread_state (I.prefix (I.prefix il j) i) (thread_id_of (I.prefix il j) i); 
    (==) {}
      thread_state_pre (I.prefix il j) i;
    }

let lemma_thread_state_post_prefix (#vcfg:_) (il:its_log vcfg) (j:nat{ j <= I.length il}) (i:I.seq_index il { i < j })
  : Lemma (thread_state_post il i == thread_state_post (I.prefix il j) i)
  = lemma_thread_state_pre_prefix il j i;
    I.lemma_prefix_index il j i

let lemma_verifier_thread_state_frame #vcfg (il: its_log vcfg { I.length il > 0 })
                                            (tid: valid_tid il)
  : Lemma (requires (tid <> thread_id_of il (I.length il - 1)))
          (ensures (thread_state il tid == thread_state (I.hprefix il) tid))
  = let last = I.length il - 1 in
    I.lemma_prefix_snoc il last;
    I.prefix_identity il

let forall_store_ismap (#vcfg:_) (ils:its_log vcfg) =
  forall_store_ismap_0 ils /\
  (forall (i:nat{i < I.length ils}). {:pattern (I.prefix ils i)}
     forall_store_ismap_0 (I.prefix ils i))

let elim_forall_store_ismap (#vcfg:_) (ils:its_log vcfg) = ()

let lemma_forall_store_ismap_extend_hprefix_0 (#vcfg:_) (il:its_log vcfg{I.length il > 0})
  : Lemma (requires (forall_store_ismap (I.hprefix il) /\ 
                     is_map (thread_store (thread_state_post il (length il - 1)))))
          (ensures (forall_store_ismap_0 il))
  = let il' = I.hprefix il in
    let last = length il - 1 in
    let last_tid = thread_id_of il last in
    let aux (tid:valid_tid il)
      : Lemma (ensures is_map (thread_store (thread_state il tid)))
              (decreases (IL?.prf il))
              [SMTPat (thread_state il tid)]
      = if tid <> last_tid
        then (
          lemma_verifier_thread_state_frame il tid;
          assert (thread_state il tid == thread_state il' tid)
        )
        else (
          calc
          (==) {
            thread_state il tid;
          (==) { I.prefix_identity il }
            thread_state_post il last;
          }
        )
    in
    ()

let lemma_forall_store_ismap_extend_hprefix (#vcfg:_) (il:its_log vcfg{I.length il > 0})
  : Lemma (requires (forall_store_ismap (I.hprefix il) /\ 
                     forall_store_ismap_0 il))
          (ensures (forall_store_ismap il))
  = let aux (i:nat{i < I.length il})
      : Lemma (forall_store_ismap_0 (I.prefix il i))
              [SMTPat (I.prefix il i)]
      = I.lemma_prefix_prefix il (I.length il - 1) i
    in
    ()

let lemma_forall_store_ismap_extend (#vcfg:_) (il:its_log vcfg) (i:I.seq_index il)
  : Lemma (requires (forall_store_ismap (I.prefix il i) /\ 
                     is_map (thread_store (thread_state_post il i))))
          (ensures (forall_store_ismap (I.prefix il (i + 1)))) 
  = I.lemma_prefix_prefix il (i + 1) i;
    let il_i' = I.prefix il (i + 1) in
    lemma_thread_state_post_prefix il (i + 1) i;
    lemma_forall_store_ismap_extend_hprefix_0 (I.prefix il_i' (i + 1));
    lemma_forall_store_ismap_extend_hprefix (I.prefix il_i' (i + 1))

let forall_vtls_rel #vcfg ils =      
    forall_vtls_rel_0 ils /\
    (forall (i:nat { i < I.length ils }). {:pattern (I.prefix ils i)} forall_vtls_rel_0 (I.prefix ils i))

let elim_forall_vtls_rel (#vcfg:_) (ils:its_log vcfg) 
  : Lemma (requires forall_vtls_rel ils)
          (ensures forall_vtls_rel_0 ils)
          [SMTPat (forall_vtls_rel ils)]
  = ()

let lemma_forall_vtls_rel_extend_hprefix_0 (#vcfg:_) (ils:its_log vcfg{ I.length ils > 0 })
  : Lemma (requires (let i = I.length ils - 1 in
                     let ils_i = I.hprefix ils in
                     let ilk = to_logk ils in
                     let ilk_i = I.hprefix ilk in                     
                     forall_vtls_rel ils_i /\
                     vtls_rel (thread_state_post ils i) 
                              (SpecTS.thread_state_post ilk i)))
          (ensures (forall_vtls_rel_0 ils))
  = let i = I.length ils - 1 in
    let ils_i = I.hprefix ils in
    let ilk = to_logk ils in
    let ilk_i = I.hprefix ilk in                     
    let aux (tid:valid_tid ils)
      : Lemma (vtls_rel (thread_state ils tid) (SpecTS.thread_state ilk tid))
              [SMTPat (SpecTS.thread_state ilk tid)]
      = let tid_i = thread_id_of ils i in
        assert (SpecTS.thread_id_of ilk i == tid_i);
        if tid_i = tid
        then ( 
          I.prefix_identity ils;
          I.prefix_identity ilk;
          assert (thread_state ils tid == thread_state_post ils i);
          assert (SpecTS.thread_state ilk tid == SpecTS.thread_state_post ilk i)
        )
        else (
          lemma_verifier_thread_state_frame ils tid;
          SpecTS.lemma_verifier_thread_state_frame ilk tid
        )
    in
    ()

let lemma_forall_vtls_rel_extend_hprefix (#vcfg:_) (ils:its_log vcfg{ I.length ils > 0 })
  : Lemma (requires (forall_vtls_rel (I.hprefix ils) /\
                     forall_vtls_rel_0 ils))
          (ensures (forall_vtls_rel ils))
  = let aux (i:nat{i < I.length ils})
      : Lemma (forall_vtls_rel_0 (I.prefix ils i))
              [SMTPat (I.prefix ils i)]
      = I.lemma_prefix_prefix ils (I.length ils - 1) i
    in
    ()

let lemma_forall_vtls_rel_extend (#vcfg:_) (ils:its_log vcfg) (i:I.seq_index ils)
  : Lemma (requires (let ils_i = I.prefix ils i in
                     let ilk = to_logk ils in
                     let ilk_i = I.prefix ilk i in                     
                     forall_vtls_rel ils_i /\
                     vtls_rel (thread_state_post ils i) 
                              (SpecTS.thread_state_post ilk i)))
          (ensures (let ils_i1 = I.prefix ils (i + 1) in
                    forall_vtls_rel ils_i1)) 
  = let ilk = to_logk ils in
    I.lemma_prefix_prefix ils (i + 1) i;
    lemma_thread_state_post_prefix ils (i + 1) i;
    lemma_to_logk_prefix_commute ils (i + 1);
    SpecTS.lemma_thread_state_post_prefix (to_logk ils) (i + 1) i;
    lemma_forall_vtls_rel_extend_hprefix_0 (I.prefix ils (i + 1));
    lemma_forall_vtls_rel_extend_hprefix (I.prefix ils (i + 1))

module Spec = Veritas.Verifier
let lemma_forall_vtls_rel_hprefix (#vcfg:_) (ils:its_log vcfg{I.length ils > 0})
                                                         
  : Lemma (requires forall_vtls_rel ils)
          (ensures forall_vtls_rel (I.hprefix ils))
  = ()          
          
module VVG = Veritas.Verifier.Global
module VVT = Veritas.Verifier.Thread
let lemma_forall_vtls_rel_implies_spec_verifiable (#vcfg:_) (ils:its_log vcfg)
  : Lemma (requires (forall_vtls_rel ils))
          (ensures (let ilk = to_logk ils in
                    SpecTS.verifiable ilk))
  = let ilk = to_logk ils in
    let aux (tid: valid_tid ils)
      : Lemma (VVT.verifiable (VVG.thread_log (I.s_seq ilk) tid))
              [SMTPat (VVG.thread_log (I.s_seq ilk) tid)]
      = assert (vtls_rel (thread_state ils tid) (SpecTS.thread_state ilk tid));
        SpecTS.reveal_thread_state ilk tid
    in
    ()

let lemma_thread_log_prefix (#vcfg:_) (ils:its_log vcfg) (i:I.seq_index ils)
  : Lemma (let tid = thread_id_of ils i in
           let ix = i2s_map ils i in
           IntG.thread_log (I.s_seq (I.prefix ils (i + 1))) tid ==
           IntT.prefix (IntG.thread_log (I.s_seq ils) tid) (snd ix + 1))
  = let tid = thread_id_of ils i in
    let ix = i2s_map ils i in
    assert (fst (IntG.thread_log (I.s_seq (I.prefix ils (i + 1))) tid) ==
            fst (IntT.prefix (IntG.thread_log (I.s_seq ils) tid) (snd ix + 1)));
    calc 
    (==) {
      snd (IntG.thread_log (I.s_seq (I.prefix ils (i + 1))) tid);
    (==) {} 
      Seq.index (I.s_seq (I.prefix ils (i + 1))) tid;
    (==) { I.interleave_sseq_index_next ils i }
      SA.prefix (Seq.index (I.s_seq ils) tid) (snd ix + 1);
    }
    
let lemma_clock_thread_state (#vcfg:_) (ils:its_log vcfg { forall_vtls_rel ils }) (i:I.seq_index ils)
  : Lemma (let tid = thread_id_of ils i in
           clock ils i == Valid?.clock (thread_state (I.prefix ils (i + 1)) tid))
  = let tid = thread_id_of ils i in
    let is = i2s_map ils i in
    let tl = thread_log (I.s_seq ils) tid in
    let ils_i = I.prefix ils (i + 1) in
    calc 
    (==) {
      clock ils i;
    (==) {}
      IntG.clock (I.s_seq ils) is;
    (==) {} 
      IntT.clock tl (snd is);
    (==) {}
      Valid?.clock (IntT.verify (IntT.prefix tl (snd is + 1)));
    };
    calc
    (==) {
      thread_state ils_i tid;
    (==) { }
      IntT.verify (IntG.thread_log (I.s_seq ils_i) tid);
    };
    lemma_thread_log_prefix ils i;
    assert (IntG.thread_log (I.s_seq ils_i) tid ==
            IntT.prefix tl (snd is + 1))

let lemma_thread_state_spec (ilk:SpecTS.il_vlog) (i:I.seq_index ilk)
  : Lemma (let ix = i2s_map ilk i in           
           let tid = fst ix in
           let tl = VVG.thread_log (I.s_seq ilk) tid in
           let ts = SpecTS.thread_state (I.prefix ilk (i + 1)) tid in
           let ts' = VVT.verify (VVT.prefix tl (snd ix + 1)) in
           ts == ts')
  = let ix = i2s_map ilk i in
    let tid = fst ix in
    let ilk_i = I.prefix ilk (i + 1) in
    let ts = SpecTS.thread_state ilk_i tid in
    SpecTS.lemma_thread_state_post_prefix ilk (i + 1) i;
    let tl = VVG.thread_log (I.s_seq ilk) tid in
    SpecTS.reveal_thread_state ilk_i tid;
    I.interleave_sseq_index_next ilk i
  
let lemma_clock_thread_state_spec (#vcfg:_) (ils:its_log vcfg { forall_vtls_rel ils }) (i:I.seq_index ils)
  : Lemma (let tid = thread_id_of ils i in
           let ilk = to_logk ils in
           let ts = (SpecTS.thread_state (I.prefix ilk (i + 1)) tid) in
           Spec.Valid? ts /\
           SpecTS.clock ilk i == Spec.Valid?.clk ts)
  = let tid = thread_id_of ils i in
    let ilk = to_logk ils in
    let ts = SpecTS.thread_state (I.prefix ilk (i + 1)) tid in
    SpecTS.lemma_thread_state_post_prefix ilk (i + 1) i;
    I.prefix_identity ils;
    assert (forall_vtls_rel_0 (I.prefix ils (i + 1)));
    let ils_i = (I.prefix ils (i + 1)) in
    assert (vtls_rel (thread_state ils_i tid) (SpecTS.thread_state (to_logk ils_i) tid));
    lemma_to_logk_prefix_commute ils (i + 1);
    assert (vtls_rel (thread_state ils_i tid) ts);
    assert (Spec.Valid? ts);
    lemma_thread_state_spec ilk i

let lemma_spec_clock (#vcfg:_) (ils:its_log vcfg { forall_vtls_rel ils }) (i:I.seq_index ils)
  : Lemma (let ilk = to_logk ils in
           SpecTS.clock ilk i == clock ils i)
  = I.prefix_identity ils;
    let ilk = to_logk ils in
    let ils_i = I.prefix ils (i + 1) in
    assert (forall_vtls_rel_0 ils_i);
    let ilk_i = to_logk ils_i in
    let tid = thread_id_of ils i in
    assert (vtls_rel (thread_state ils tid)  (SpecTS.thread_state ilk tid) );
    assert (Spec.Valid? (SpecTS.thread_state ilk tid));
    lemma_clock_thread_state ils i;
    lemma_clock_thread_state_spec ils i;
    assert (vtls_rel (thread_state ils_i tid)  (SpecTS.thread_state ilk_i tid));
    lemma_to_logk_prefix_commute ils (i + 1);
    assert (clock ils i == Valid?.clock (thread_state ils_i tid));
    assert (SpecTS.clock ilk i == Spec.Valid?.clk (SpecTS.thread_state ilk_i tid))


let lemma_vtls_rel_implies_spec_clock_sorted (#vcfg:_) (ils:its_log vcfg)
  : Lemma (requires (forall_vtls_rel ils))
          (ensures (let ilk = to_logk ils  in
                    SpecTS.clock_sorted ilk))
  = let ilk = to_logk ils in
    assert (clock_sorted ils);
    let aux (i j:I.seq_index ilk)
      : Lemma (requires i <= j)
              (ensures SpecTS.clock ilk i `ts_leq` SpecTS.clock ilk j)
              [SMTPat (SpecTS.clock ilk i);
               SMTPat (SpecTS.clock ilk j)]
      = lemma_spec_clock ils i;
        lemma_spec_clock ils j
    in
    ()

let lemma_vtls_rel_implies_hash_verifiable (#vcfg:_) (ils:hash_verifiable_log vcfg)
  : Lemma (requires (forall_vtls_rel ils))
          (ensures (let ilk = to_logk ils in
                    SpecTS.hash_verifiable ilk))
  = let ilk = to_logk ils in
    calc
    (==) {
      SpecTS.hash_verifiable ilk;
    (==) { }
      VVG.hash_verifiable (I.s_seq ilk);
    (==) { }
      (VVG.hadd (I.s_seq ilk) = VVG.hevict (I.s_seq ilk));
    };
    admit();
    calc
    (==) {
      VVG.hadd (I.s_seq ilk);
    (==) { }
      IntG.hadd (I.s_seq ils);
    };

    calc
    (==) {
      VVG.hevict (I.s_seq ilk);
    (==) { }
      IntG.hevict (I.s_seq ils);
    }




let lemma_empty_implies_spec_rel (#vcfg:_) (ils:its_log vcfg{I.length ils = 0})
  : Lemma (spec_rel ils) 
  = admit()

let lemma_spec_rel_implies_prefix_spec_rel (#vcfg:_) (ils:its_log vcfg) (i:nat{i <= I.length ils})
 : Lemma (requires spec_rel ils)
         (ensures (let ils' = I.prefix ils i in
                   spec_rel ils')) = I.prefix_identity ils

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
                         
let lemma_clock_ordering (#vcfg:_) (itsl: its_log vcfg) (i1 i2: I.seq_index itsl)
  : Lemma (requires (clock itsl i1 `ts_lt` clock itsl i2))
          (ensures (i1 < i2)) 
  = assert (verifiable itsl);
    assert (clock_sorted itsl);
    if i2 <= i1
    then  assert (clock itsl i2 `ts_leq` clock itsl i1)

