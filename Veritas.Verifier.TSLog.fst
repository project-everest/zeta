module Veritas.Verifier.TSLog

module VG = Veritas.Verifier.Global

let clock_sorted (il: il_vlog{verifiable il}) =
 forall (i j:I.seq_index il). i <= j ==> clock il i `ts_leq` clock il j

module SA = Veritas.SeqAux
open FStar.Calc

let lemma_prefix_clock_sorted (itsl: its_log) (i:nat{i <= I.length itsl})
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
        //This "calc" feature lets you structure
        //proofs by equational rewriting ... each line is
        //equal to the next line and the whole calc term
        //proves that the first line is equal to the last
        //
        calc (==) {
         clock itsl' t0;
          == {}
         clock (I.prefix itsl i) t0;
          == {}
         VG.clock (g_vlog_of itsl') (i2s_map itsl' t0);
          == {}
         VG.clock (g_vlog_of itsl') (i2s_map itsl t0);
        }
    in
    ()

let lemma_prefix_verifiable (itsl: its_log) (i:nat{i <= I.length itsl})
  : Lemma
    (ensures
      verifiable (I.prefix itsl i) /\
      clock_sorted (I.prefix itsl i))
  = assert (verifiable itsl);
    assert (clock_sorted itsl);
    let ss = g_vlog_of itsl in
    let itsl' = I.prefix itsl i in
    let ss' = g_vlog_of itsl' in
    assert (Seq.length ss = Seq.length ss');
    let aux (tid:SA.seq_index ss)
      : Lemma (VT.verifiable (thread_log ss' tid))
              [SMTPat (thread_log ss' tid)]
      = let tl = thread_log ss tid in
        assert (VT.verifiable tl);
        I.per_thread_prefix itsl i;
        let tl' = thread_log ss' tid in
        let aux (j:SA.seq_index (snd tl))
          : Lemma
            (requires snd tl' == SA.prefix (snd tl) j)
            (ensures VT.verifiable tl')
            [SMTPat (SA.prefix (snd tl) j)]
          = assert (tl' == VT.prefix tl j);
            VT.lemma_verifiable_implies_prefix_verifiable tl j
        in
        ()
    in
    lemma_prefix_clock_sorted itsl i


#push-options "--fuel 0,0"

let sseq_same_shape #a #b (s0:sseq a) (s1:sseq b) = 
  Seq.length s0 = Seq.length s1 /\
  (forall (i:seq_index s0). Seq.length (Seq.index s0 i) = Seq.length (Seq.index s1 i))


let mapi (#a #b:_) (s:seq a) (f:(seq_index s -> b))
  : t:seq b{
    Seq.length s == Seq.length t /\
    (forall (i:seq_index s). Seq.index t i == f i)
   }
  = Seq.init (Seq.length s) f

let sseq_append #a (ss0:sseq a) (ss1:sseq a{Seq.length ss0 == Seq.length ss1}) 
  : sseq a 
  = mapi ss0 (fun i -> Seq.append (Seq.index ss0 i) (Seq.index ss1 i))

let ts_sorted_seq (s:seq (vlog_entry & timestamp)) = 
  forall (i j:seq_index s).
    i <= j ==>
    snd (Seq.index s i) `ts_leq` snd (Seq.index s j)

let ts_sseq = 
    s:sseq (vlog_entry & timestamp) {
      forall (i:seq_index s). ts_sorted_seq (Seq.index s i)
    }

let is_min_clock_up_to (s:ts_sseq) (i:nat{ i <= Seq.length s }) (min:sseq_index s)
  =  snd min == 0 /\
     (forall (j:sseq_index s). 
       fst j < i ==> snd (indexss s min) `ts_leq` snd (indexss s j))
    
let min_clock_up_to (s:ts_sseq) (i:nat{ i <= Seq.length s }) =
    min:sseq_index s { is_min_clock_up_to s i min }

let min_clock s = min_clock_up_to s (Seq.length s)

let rec pick_min (s:ts_sseq)
                 (i:nat{i <= Seq.length s})
                 (min:min_clock_up_to s i)
  : Tot (min_clock s)
        (decreases (Seq.length s - i))
  = if i = Seq.length s then min
    else (
      if Seq.length (Seq.index s i) = 0
      then pick_min s (i + 1) min
      else (
        if snd (indexss s (i, 0)) `ts_leq`
           snd (indexss s min)
        then pick_min s (i + 1) (i,0)
        else (assert (snd (indexss s min) `ts_leq`
                      snd (indexss s (i, 0)));
              assert (forall (j:sseq_index s). 
                        fst j = i /\
                        snd j >= 0 ==>
                        snd (indexss s min) `ts_leq` 
                        snd (indexss s (i,0)) /\
                        snd (indexss s (i,0)) `ts_leq`
                        snd (indexss s j));
              pick_min s (i + 1) min
        )
      )
    )

let is_empty_sseq #a (s:sseq a) =
    forall (i:seq_index s). Seq.index s i `Seq.equal` empty #a

let rec min_sseq_index(s:ts_sseq)
  : Tot (o:option (sseq_index s) {
        match o with
        | None -> is_empty_sseq s
        | Some min -> is_min_clock_up_to s 0 min
        })
        (decreases (Seq.length s))
  = if Seq.length s = 0 then None
    else let prefix, last = Seq.un_snoc s in
         match min_sseq_index prefix with
         | None -> 
           if Seq.length last = 0 
           then None
           else (
             let min = (Seq.length s - 1, 0) in
             Some min
           )
         | Some i ->
           Some i

#push-options "--z3rlimit_factor 8"
let flat_length_single #a (s:seq a)
  : Lemma (flat_length (create 1 s) == Seq.length s)
  = assert (Seq.equal (create 1 s) (append1 empty s));
    lemma_flat_length_app1 empty s;
    lemma_flat_length_empty #a
  
let split_ts_sseq (s:ts_sseq) 
  : o:option (i:min_clock s &
              e:(vlog_entry & timestamp){e == indexss s i} &
              s':ts_sseq {
                Seq.length s = Seq.length s' /\
                s `Seq.equal` Seq.upd s (fst i)
                              (Seq.cons e (Seq.index s' (fst i))) /\
                flat_length s' < flat_length s
             }){
       None? o ==> is_empty_sseq s
    }
  = match min_sseq_index s with
    | None -> None
    | Some min ->
      let j = pick_min s 0 min in
      let e = Seq.head (Seq.index s (fst j)) in
      let tl_j = Seq.tail (Seq.index s (fst j)) in
      let s' = Seq.upd s (fst j) tl_j in
      assert (length (Seq.index s (fst j)) == length (Seq.index s' (fst j)) + 1);
      let s'_prefix, s'_suffix = Seq.split s' (fst j) in
      let s_prefix, s_suffix = Seq.split s (fst j) in
      assert (s_prefix == s'_prefix);
      let x', s'_suffix' = Seq.head s'_suffix, Seq.tail s'_suffix in
      let x, s_suffix' = Seq.head s_suffix, Seq.tail s_suffix in      
      assert (s'_suffix' == s_suffix');
      assert (Seq.length x' < Seq.length x);
      lemma_flat_length_app s'_prefix s'_suffix;
      lemma_flat_length_app s_prefix s_suffix;      
      assert (s'_suffix `Seq.equal` Seq.cons x' s'_suffix');
      assert (s_suffix `Seq.equal` Seq.cons x s_suffix');      
      assert (s' `Seq.equal` (Seq.append s'_prefix s'_suffix));
      assert (s `Seq.equal` (Seq.append s_prefix s_suffix));      
      // assert (flat_length s' == flat_length s'_prefix + flat_length s'_suffix);
      // assert (flat_length s == flat_length s_prefix + flat_length s_suffix);      
      lemma_flat_length_app (create 1 x') s'_suffix';
      // assert (flat_length s'_suffix == flat_length (create 1 x') + flat_length s'_suffix');
      lemma_flat_length_app (create 1 x) s'_suffix';      
      // assert (flat_length s_suffix == flat_length (create 1 x) + flat_length s'_suffix');      
      flat_length_single x;
      flat_length_single x';      
      assert (flat_length s' < flat_length s);
      Some (| j, e, s' |)
#pop-options
let ts_seq = s:seq (vlog_entry & timestamp){ ts_sorted_seq s }

let get_min_clock (s:ts_sseq { ~(is_empty_sseq s) })
  : ts:timestamp {
      forall (i:sseq_index s). ts `ts_leq` snd (indexss s i)
    }
  = let Some (| _, e, _|) = split_ts_sseq s in
    snd e

let clock_exceeds (s0:ts_seq) (ts:timestamp) =
  forall (i:seq_index s0). snd (Seq.index s0 i) `ts_leq` ts

module I = Veritas.Interleave

let coerce_interleave (#a:eqtype) (s:seq a) (s0 s1:sseq a) (i:interleave s s0 { Seq.equal s0 s1 })
  : interleave s s1
  = i

#push-options "--z3rlimit_factor 2"
let rec interleave_ts_sseq 
         (s0:ts_seq)
         (ss0:ts_sseq) 
         (ss1:ts_sseq {
           (Seq.length ss0 == Seq.length ss1) /\
           (is_empty_sseq ss1 \/
            (clock_exceeds s0 (get_min_clock ss1) /\
             (forall (i:seq_index ss0). 
               clock_exceeds (Seq.index ss0 i) (get_min_clock ss1))))
          })
         (prefix:interleave s0 ss0)
   : Tot (s:ts_seq &
          interleave s
                     (ss0 `sseq_append` ss1))
         (decreases (flat_length ss1))
   = match split_ts_sseq ss1 with
     | None ->
       assert (is_empty_sseq ss1);
       assert (forall (i:seq_index ss0). 
               Seq.equal (Seq.index ss0 i)
                         (Seq.append (Seq.index ss0 i) empty));
       assert (Seq.equal ss0 (ss0 `sseq_append` ss1));
       (| s0, prefix |)
       
     | Some (| i, e, ss1' |) ->
       let s0' : ts_seq = append1 s0 e in
       let prefix' : interleave (append1 s0 e) (sseq_extend ss0 e (fst i)) 
         = I.IntExtend s0 ss0 prefix e (fst i)
       in
       let ss0' = sseq_extend ss0 e (fst i) in
       let aux (j:seq_index ss0)
         : Lemma 
           (ensures (Seq.index (sseq_append ss0' ss1') j `Seq.equal` Seq.index (sseq_append ss0 ss1) j))
           [SMTPat (Seq.index (sseq_append ss0' ss1') j)]
         = let v = sseq_append ss0 ss1 in
           let v' = sseq_append ss0' ss1' in
           if fst i <> j 
           then ()
           else (
             assert (Seq.index v j == Seq.append (Seq.index ss0 j) (Seq.index ss1 j));
             assert (Seq.index ss1' j == Seq.tail (Seq.index ss1 j));
             assert (Seq.index ss0' j == Seq.snoc (Seq.index ss0 j) (Seq.head (Seq.index ss1 j)))
           )
       in
       assert ((sseq_append ss0' ss1') `Seq.equal` (sseq_append ss0 ss1));
       let aux (j:seq_index ss0')
         : Lemma (ensures ts_sorted_seq (Seq.index ss0' j))
                 [SMTPat (Seq.index ss0' j)]
         = if fst i <> j
           then () 
           else (
             assert (Seq.index ss0' j == Seq.snoc (Seq.index ss0 j) (Seq.head (Seq.index ss1 j)));
             assert (Seq.head (Seq.index ss1 j) == e);
             assert (clock_exceeds (Seq.index ss0' j) (snd e))
           )
       in
       assert (forall (i:seq_index ss0'). ts_sorted_seq (Seq.index ss0' i));
       let aux ()
         : Lemma (requires ~(is_empty_sseq ss1'))
                 (ensures (clock_exceeds s0' (get_min_clock ss1')))
                 [SMTPat()]
         = assert (snd e `ts_leq` (get_min_clock ss1'));
           assert (s0' == Seq.snoc s0 e);
           assert (clock_exceeds s0 (snd e));
           assert (forall (i:seq_index s0').
                     snd (Seq.index s0' i) `ts_leq` (snd e) /\
                     snd e `ts_leq` (get_min_clock ss1'))
       in
       let aux (j:seq_index ss0')
         : Lemma (requires ~(is_empty_sseq ss1'))
                 (ensures (clock_exceeds (Seq.index ss0' j) (get_min_clock ss1')))
                 [SMTPat()]
         = assert (clock_exceeds (Seq.index ss0 j) (get_min_clock ss1));
           assert (clock_exceeds (Seq.index ss0 j) (snd e));
           assert (snd e `ts_leq` get_min_clock ss1');
           if fst i <> j 
           then (
             assert (Seq.index ss0 j == Seq.index ss0' j)
           )
           else (
             assert (Seq.index ss0' j == Seq.snoc (Seq.index ss0 j) e);
             let ss = Seq.index ss0' j in
             assert (forall (i:seq_index ss).
                     snd (Seq.index ss i) `ts_leq` (snd e) /\
                     snd e `ts_leq` (get_min_clock ss1'));
             ()
           )
       in
       let (| s, p |) = interleave_ts_sseq s0' ss0' ss1' prefix' in
       (| s, coerce_interleave s _ _ p |)
#pop-options

let create_tsseq_interleaving (ss:ts_sseq)
  : (s:ts_seq & interleave s ss)
  = let (| s, i |) = interleave_ts_sseq empty (create (Seq.length ss) empty) ss (interleave_empty_n _) in
    assert (forall (i:seq_index ss). 
           Seq.index ((create (Seq.length ss) empty) `sseq_append` ss) i 
           `Seq.equal`
           Seq.index ss i);
    assert (((create (Seq.length ss) empty) `sseq_append` ss) `Seq.equal` ss);
    (| s, coerce_interleave _ _ _ i |)
    
let with_clock_i (vl:VG.verifiable_log) (i:seq_index vl)
  : s:ts_seq {
      Seq.length s = Seq.length (Seq.index vl i) /\
      (forall (j:seq_index s). (indexss vl (i,j), VG.clock vl (i,j)) == Seq.index s j)
    }
  = let vl_i = Seq.index vl i in
    let s = mapi vl_i (fun j -> Seq.index vl_i j, VG.clock vl (i, j)) in
    let aux (a b:seq_index s)
      : Lemma 
        (requires a <= b)
        (ensures snd (Seq.index s a) `ts_leq` snd (Seq.index s b))
        [SMTPat (Seq.index s a);
         SMTPat (Seq.index s b)]
      = VT.lemma_clock_monotonic (VG.thread_log vl i) a b
    in
    s
  
let ts_seq_of_g_vlog (vl:VG.verifiable_log)
  : s:ts_sseq {
      sseq_same_shape vl s /\
      (forall (i:sseq_index s). 
         indexss s i == (indexss vl i, VG.clock vl i))
    }
  = mapi vl (with_clock_i vl)

let map_tsseq (f:(vlog_entry & timestamp) -> 'a) (x:ts_sseq) 
  : sseq 'a
  = map (map f) x

let g_vlog_of_ts_sseq (x:ts_sseq)
  : g_vlog
  = map_tsseq fst x
  
let inverse_g_vlog_ts_seq (vl:VG.verifiable_log)
  : Lemma (g_vlog_of_ts_sseq (ts_seq_of_g_vlog vl) == vl)
  = let ts = ts_seq_of_g_vlog vl in
    let vl' = g_vlog_of_ts_sseq ts in
    assert (Seq.length ts == Seq.length vl');
    let aux (i:seq_index ts)
      : Lemma (ensures Seq.index vl' i `Seq.equal` Seq.index vl i)
              [SMTPat (Seq.index vl i)]
      = ()
    in
    assert (Seq.equal vl' vl)
  
let create (gl:VG.verifiable_log)
  = let ts = ts_seq_of_g_vlog gl in
    let (| s, tsi |) = create_tsseq_interleaving ts in
    inverse_g_vlog_ts_seq gl;
    let il = IL _ gl (map_interleave fst _ _ tsi) in
    assert (verifiable il);
    assert (g_vlog_of il == gl);
    let aux (i j: I.seq_index il)
      : Lemma (requires i <= j)
              (ensures clock il i `ts_leq` clock il j)
              [SMTPat (clock il i `ts_leq` clock il j)]
      = let i' = i2s_map il i in
        let j' = i2s_map il j in
        map_interleave_i2s fst (IL _ _ tsi) i;
        map_interleave_i2s fst (IL _ _ tsi) j;        
        assert (VG.clock gl i' == snd (indexss ts i'));
        assert (VG.clock gl j' == snd (indexss ts j'));        
        lemma_i2s_s2i il i;
        lemma_i2s_s2i il j;        
        assert (indexss ts i' == index s (s2i_map il i'));        
        assert (indexss ts j' == index s (s2i_map il j'));                
        assert (indexss ts i' == index s i);
        assert (indexss ts j' == index s j);        
        assert (VG.clock gl i' `ts_leq` VG.clock gl j')
    in
    assert (clock_sorted il);
    il

(*thread state after processing ts log - guaranteed to be valid *)
let thread_state (itsl: its_log) 
                 (tid: valid_tid itsl) 
  : Tot (vs:vtls{Valid? vs})
  = verify (thread_log (s_seq itsl) tid)

#push-options "--fuel 1,1"
let t_verify_aux_snoc (vs:vtls) (l:vlog) (e:vlog_entry)
  : Lemma (ensures 
             t_verify_aux vs (Seq.snoc l e) ==
             t_verify_step (t_verify_aux vs l) e)
          (decreases (Seq.length l))
  = assert (prefix (Seq.snoc l e) (Seq.length l) `Seq.equal` l)
#pop-options

let lemma_verifier_thread_state_extend (itsl: its_log) (i: I.seq_index itsl)
  : Lemma (thread_state_post itsl i == 
           t_verify_step (thread_state_pre itsl i) (I.index itsl i))
  = let tid = thread_id_of itsl i in
    let itsl_i = I.prefix itsl i in
    let vlog_tid = Seq.index (s_seq itsl_i) tid in    
    let itsl_i' = I.prefix itsl (i + 1) in
    let vlog_tid' = Seq.index (s_seq itsl_i') tid in
    I.lemma_prefix_snoc itsl i;
    assert (vlog_tid' `Seq.equal` Seq.snoc vlog_tid (I.index itsl i));
    let init = init_thread_state tid in
    let lhs = t_verify_aux init vlog_tid' in
    let rhs = t_verify_step (t_verify_aux init vlog_tid) (I.index itsl i) in
    t_verify_aux_snoc init vlog_tid (I.index itsl i)

#reset-options

let mk_vlog_entry_ext (itsl:its_log) (i:I.seq_index itsl) 
  : vlog_entry_ext 
  =   let ts = thread_state_pre itsl i in
      let Valid _ st clk _ _ _  = ts in
      let vle = Seq.index (i_seq itsl) i in
      lemma_verifier_thread_state_extend itsl i;
      match vle with
      | EvictM k k' ->
        let Some (VStore v _) = st k in
        EvictMerkle vle v
      | EvictB k ts ->
        let Some (VStore v _) = st k in
        EvictBlum vle v (thread_id_of itsl i)
      | EvictBM k k' ts ->
        let Some (VStore v _) = st k in
        EvictBlum vle v (thread_id_of itsl i)
      | v -> NEvict v
let vlog_ext_of_its_log (itsl:its_log)
  : seq vlog_entry_ext
  = mapi (i_seq itsl) (mk_vlog_entry_ext itsl)
let rec map_mapi_fusion (s:seq 'a) (f:SA.seq_index s -> 'b) (g:'b -> 'c)
  : Lemma (ensures map g (mapi s f) == mapi s (fun i -> g (f i)))
          (decreases (Seq.length s))
  = if Seq.length s <> 0 then map_mapi_fusion (Seq.tail s) f g;
    assert (map g (mapi s f) `Seq.equal` mapi s (fun i -> g (f i)))

let inverse_to_vlog_vlog_ext_of_vlog_entry (itsl:its_log)
  : Lemma (to_vlog (vlog_ext_of_its_log itsl) `Seq.equal` i_seq itsl)
  = map_mapi_fusion (i_seq itsl) (mk_vlog_entry_ext itsl) to_vlog_entry
  
(* is this an evict add consistent log *)
let is_eac (itsl: its_log) : bool =
  Veritas.EAC.is_eac (vlog_ext_of_its_log itsl)


#push-options "--query_stats --ifuel 1,1"
let vlog_ext_of_prefix (itsl:its_log) (i:nat { i <= I.length itsl })
  : Lemma (vlog_ext_of_its_log (I.prefix itsl i) `prefix_of`
           vlog_ext_of_its_log itsl)
  = let itsl_i = I.prefix itsl i in
    let mk_vlog_entry_ext_prefix (j:I.seq_index itsl{ j < i })
        : Lemma (ensures mk_vlog_entry_ext itsl j == mk_vlog_entry_ext itsl_i j)
                [SMTPat (mk_vlog_entry_ext itsl_i j)]
        = assert (Seq.index (i_seq itsl) j == Seq.index (i_seq itsl_i) j);
          I.lemma_i2s_map_prefix itsl i j;
          I.lemma_prefix_prefix itsl i j;
          assert (thread_id_of itsl j == thread_id_of itsl_i j)
    in
    let lhs = vlog_ext_of_its_log (I.prefix itsl i) in
    let rhs = vlog_ext_of_its_log itsl in
    assert (lhs `Seq.equal` SA.prefix rhs (Seq.length lhs))

let eac_boundary (itsl: neac_log)
  : i:I.seq_index itsl{is_eac (I.prefix itsl i) &&
                       not (is_eac (I.prefix itsl (i + 1)))}
  = let vl = vlog_ext_of_its_log itsl in
    let i = max_valid_all_prefix eac_sm vl in
    assert (~ (eac vl));
    assert (i < length vl);
    assert (Veritas.EAC.is_eac (prefix vl i));
    assert (~ (Veritas.EAC.is_eac (prefix vl (i + 1))));
    vlog_ext_of_prefix itsl i;
    vlog_ext_of_prefix itsl (i + 1);    
    i            
  
(* if itsl is eac, then any prefix is also eac *)
let lemma_eac_implies_prefix_eac (itsl: eac_log) (i:nat {i <= I.length itsl})
  : Lemma (ensures (is_eac (I.prefix itsl i)))
  = let vlog = vlog_ext_of_its_log itsl in
    let vlog' = vlog_ext_of_its_log (I.prefix itsl i) in
    vlog_ext_of_prefix itsl i;
    lemma_valid_all_prefix eac_sm vlog (Seq.length vlog')
  
(* if the ts log is eac, then its state ops are read-write consistent *)
let lemma_eac_implies_state_ops_rw_consistent (itsl: eac_log)
  : Lemma (rw_consistent (state_ops itsl))
  = let vl = vlog_ext_of_its_log itsl in
    lemma_eac_implies_rw_consistent vl;
    inverse_to_vlog_vlog_ext_of_vlog_entry itsl;
    assert (rw_consistent (to_state_op_vlog (to_vlog vl)))
  
(* the eac state of a key at the end of an its log *)
let eac_state_of_key (itsl: its_log) (k:key): eac_state 
  = seq_machine_run (seq_machine_of eac_sm)
                    (partn eac_sm k (vlog_ext_of_its_log itsl))

let lemma_eac_state_of_key_valid (itsl: eac_log) (k:key)
  : Lemma (EACFail <> eac_state_of_key itsl k)
  = ()

(* the extended vlog entry to use for eac checking *)
let vlog_entry_ext_at (itsl: its_log) (i:I.seq_index itsl): 
                      (e:vlog_entry_ext{E.to_vlog_entry e = I.index itsl i})
  = Seq.index (vlog_ext_of_its_log itsl) i

#push-options "--fuel 0,0 --ifuel 0,0"

let vlog_entry_ext_at_prefix (itsl: its_log) (i:I.seq_index itsl) (j:nat { i < j /\ j <= I.length itsl })
  : Lemma (vlog_entry_ext_at itsl i ==
           vlog_entry_ext_at (I.prefix itsl j) i)
  = vlog_ext_of_prefix itsl j;
    lemma_prefix_index (vlog_ext_of_its_log itsl) j i

(* the eac state transition induced by the i'th entry *)
let lemma_eac_state_transition (itsl: its_log) (i:I.seq_index itsl)
  : Lemma (eac_state_post itsl i = 
           eac_add (vlog_entry_ext_at itsl i) (eac_state_pre itsl i))
  = let k = key_at itsl i in
    let itsl_i' = I.prefix itsl (i+1) in
    let itsl_i = I.prefix itsl i in
    let vl_i' = vlog_ext_of_its_log itsl_i' in
    let vl_i = vlog_ext_of_its_log itsl_i in
    I.lemma_prefix_prefix itsl (i + 1) i;
    assert (itsl_i == I.prefix itsl_i' i);
    vlog_ext_of_prefix itsl_i' i;
    assert (vl_i `prefix_of` vl_i');
    assert (Seq.length vl_i == i);
    assert (Seq.length vl_i' == i + 1);    
    assert (Seq.index vl_i' i == vlog_entry_ext_at itsl_i' i);
    assert (Seq.index (i_seq itsl_i') i == 
            Seq.index (i_seq itsl) i);
    vlog_entry_ext_at_prefix itsl i (i + 1);            
    assert (Seq.index vl_i' i == vlog_entry_ext_at itsl i);
    assert (vl_i' `Seq.equal` Seq.snoc vl_i (vlog_entry_ext_at itsl i));
    lemma_filter_extend2 (iskey #(key_type eac_sm) (partn_fn eac_sm) k)
                         vl_i';
    assert (partn eac_sm k vl_i' == 
            Seq.snoc (partn eac_sm k vl_i)
                     (vlog_entry_ext_at itsl i));
    let lhs = seq_machine_run (seq_machine_of eac_sm)
                              (partn eac_sm k vl_i') in
    let rhs = eac_add (vlog_entry_ext_at itsl i) 
                      (seq_machine_run (seq_machine_of eac_sm)
                                       (partn eac_sm k vl_i)) in
    lemma_reduce_append (init_state (seq_machine_of eac_sm))
                        (trans_fn (seq_machine_of eac_sm))
                        (partn eac_sm k vl_i)                        
                        (vlog_entry_ext_at itsl i);                                        
    assert (lhs == rhs)

let vlog_entry_ext_at_prefix_snoc (itsl: its_log) (i:I.seq_index itsl)
    : Lemma (vlog_ext_of_its_log (I.prefix itsl (i + 1))
             `Seq.equal` Seq.snoc (vlog_ext_of_its_log (I.prefix itsl i))
                                  (mk_vlog_entry_ext itsl i))
    = I.lemma_prefix_prefix itsl (i + 1) i;
      assert (I.prefix itsl i ==
              I.prefix (I.prefix itsl (i + 1)) i);
      let itsl_i = I.prefix itsl i in
      let itsl_i' = I.prefix itsl (i + 1) in
      let vl = vlog_ext_of_its_log itsl_i in
      let vl' = vlog_ext_of_its_log itsl_i' in
      vlog_ext_of_prefix (I.prefix itsl (i + 1)) i;
      assert (vl `prefix_of` vl');
      assert (vl' `Seq.equal` Seq.snoc vl (Seq.index vl' i));
      lemma_i2s_map_prefix itsl (i + 1) i;
      assert (thread_id_of itsl i == 
              thread_id_of (I.prefix itsl (i + 1)) i);
      assert (mk_vlog_entry_ext itsl i ==
              mk_vlog_entry_ext (I.prefix itsl (i + 1)) i)

(* if the ith entry does not involve key k, the eac state of k is unchanged *)
let lemma_eac_state_same (itsl: its_log) (i: I.seq_index itsl) (k: key):
  Lemma (requires (key_at itsl i <> k))
        (ensures (eac_state_of_key (I.prefix itsl i) k == 
                  eac_state_of_key (I.prefix itsl (i + 1)) k))
  = vlog_entry_ext_at_prefix_snoc itsl i;
    let itsl_i = I.prefix itsl i in
    let vl_i = (vlog_ext_of_its_log itsl_i) in
    let itsl_i' = I.prefix itsl (i + 1) in    
    let vl_i' = (vlog_ext_of_its_log itsl_i') in
    let lhs =
      seq_machine_run (seq_machine_of eac_sm)
                      (partn eac_sm k vl_i)
    in
    let rhs = 
      seq_machine_run (seq_machine_of eac_sm)
                      (partn eac_sm k (Seq.snoc vl_i (mk_vlog_entry_ext itsl i)))
    in
    assert (not (iskey #(key_type eac_sm) (partn_fn eac_sm) k (mk_vlog_entry_ext itsl i)));
    lemma_filter_extend1 (iskey #(key_type eac_sm) (partn_fn eac_sm) k) vl_i';
    assert (prefix vl_i' (Seq.length vl_i' - 1) `Seq.equal` vl_i)

let lemma_eac_boundary_state_transition (itsl: neac_log):
  Lemma (requires True)
        (ensures (eac_add (vlog_entry_ext_at itsl (eac_boundary itsl))
                          (eac_boundary_state_pre itsl) = EACFail))
        [SMTPat (eac_boundary itsl)]
  = let i = eac_boundary itsl in
    lemma_eac_state_transition itsl i;
    let itsl_i = (I.prefix itsl i) in
    let itsl_i' = (I.prefix itsl (i + 1)) in
    assert (is_eac itsl_i);
    assert (not (is_eac itsl_i'));
    let vl_i = vlog_ext_of_its_log itsl_i in
    let vl_i' = vlog_ext_of_its_log (I.prefix itsl (i + 1)) in
    assert (Veritas.EAC.is_eac vl_i);
    assert (not (Veritas.EAC.is_eac vl_i'));
    assert (forall k. valid (seq_machine_of eac_sm) (partn eac_sm k vl_i));
    assert (exists k. not (valid (seq_machine_of eac_sm) (partn eac_sm k vl_i')));
    let aux (k:key)
      : Lemma (requires (not (valid (seq_machine_of eac_sm) (partn eac_sm k vl_i'))))
              (ensures (key_at itsl i == k))
              [SMTPat (partn eac_sm k vl_i')]
      = let k' = key_at itsl i in
        if k' = k 
        then ()
        else (
          vlog_entry_ext_at_prefix_snoc itsl i;
          assert (vl_i' == Seq.snoc vl_i (mk_vlog_entry_ext itsl i));
          lemma_filter_extend1 (iskey #(key_type eac_sm) (partn_fn eac_sm) k) vl_i';
          assert (prefix vl_i' (Seq.length vl_i' - 1) `Seq.equal` vl_i);
          assert (partn eac_sm k vl_i' == partn eac_sm k vl_i)
        )
    in
    assert (eac_state_post itsl i == 
            eac_add (vlog_entry_ext_at itsl i) (eac_state_pre itsl i));
    ()


let eacs_t (itsl:its_log) = k:key -> e:eac_state { e == eac_state_of_key itsl k /\ (is_eac itsl ==> e <> EACFail) }
let threads_t (itsl:its_log) = t:valid_tid itsl -> v:vtls { Valid? v /\ v == verify (t, Seq.index (I.s_seq itsl) t) }
noeq 
type monitored_state (itsl:its_log) = {
  eacs: eacs_t itsl;
  threads: threads_t itsl
}

let eq_mon itsl (m0 m1: monitored_state itsl) = 
  FunctionalExtensionality.feq m0.eacs m1.eacs /\
  FunctionalExtensionality.feq m0.threads m1.threads
  
let run_monitor (itsl:its_log) 
  : monitored_state itsl 
  = let eacs : eacs_t itsl = fun k -> eac_state_of_key itsl k in
    let threads : threads_t itsl = fun t -> verify (thread_log (I.s_seq itsl) t) in
    { eacs; threads }

#push-options "--fuel 1,1"
let run_monitor_empty (itsl:its_log{I.length itsl = 0}) (k:key)
  : Lemma 
    (let m = run_monitor itsl in
     let vl = vlog_ext_of_its_log itsl in
     let vl' = partn eac_sm k vl in
     I.s_seq itsl == Seq.create (Seq.length (I.s_seq itsl)) empty /\
     m.eacs k == EACInit /\
     I.i_seq itsl == empty /\
     vl == empty /\
     vl' == empty /\
     (forall tid. thread_state itsl tid == init_thread_state tid)
     )
     
  = let m = run_monitor itsl in
    let vl = vlog_ext_of_its_log itsl in
    let vl' = partn eac_sm k vl in
    let filter_fn = iskey #(key_type eac_sm) (partn_fn eac_sm) k in 
    assert (vl `Seq.equal` empty);
    lemma_filter_empty filter_fn;
    assert (vl' `Seq.equal` empty);
    assert (Seq.equal (I.i_seq itsl) empty);
    lemma_reduce_empty EACInit (trans_fn (seq_machine_of eac_sm));
    Veritas.Interleave.interleave_empty (IL?.prf itsl)


let run_monitor_step (itsl:its_log{I.length itsl > 0}) (k:key)
  : Lemma (let i = I.length itsl - 1 in
           let itsl' = I.prefix itsl i in
           let m' = run_monitor itsl' in
           let m = run_monitor itsl in
           let v = I.index itsl i in
           let ve = mk_vlog_entry_ext itsl i in
           let vl' = vlog_ext_of_its_log itsl' in
           let vl'_k = partn eac_sm k vl' in
           let vl = vlog_ext_of_its_log itsl in
           let vl_k = partn eac_sm k vl in
           let tid = thread_id_of itsl i in
           let _, tl' = thread_log (I.s_seq (I.prefix itsl i)) tid in
           let _, tl = thread_log (I.s_seq itsl) tid in
           vl `Seq.equal` Seq.snoc vl' ve /\
           tl `Seq.equal` Seq.snoc tl' v /\
           thread_state itsl tid == t_verify_step (thread_state itsl' tid) v /\
           (if key_of v <> k 
            then vl'_k == vl_k 
            else (vl_k == Seq.snoc vl'_k ve /\
                  m.eacs k == eac_add ve (m'.eacs k))) /\
           (forall (tid':valid_tid itsl). {:pattern (thread_log (I.s_seq itsl) tid')}
             tid <> tid' ==>
             thread_log (I.s_seq itsl) tid' ==
             thread_log (I.s_seq (I.prefix itsl i)) tid'))
  = let i = I.length itsl - 1 in
    let itsl' = I.prefix itsl i in
    let m' = run_monitor itsl' in
    let m = run_monitor itsl in
    let v = I.index itsl i in
    let ve = mk_vlog_entry_ext itsl i in
    let vl' = vlog_ext_of_its_log itsl' in
    let vl'_k = partn eac_sm k vl' in
    let vl = vlog_ext_of_its_log itsl in
    let vl_k = partn eac_sm k vl in
    let tid = thread_id_of itsl i in
    let _, tl' = thread_log (I.s_seq (I.prefix itsl i)) tid in
    let _, tl = thread_log (I.s_seq itsl) tid in
    vlog_ext_of_prefix itsl i;
    I.interleave_step itsl;
    assert (vl' `prefix_of` vl);
    assert (vl `Seq.equal` Seq.snoc vl' ve);
    assert (tl `Seq.equal` Seq.snoc tl' v);
    assert (SA.prefix tl (Seq.length tl - 1) `Seq.equal` tl');
    assert (thread_state itsl tid == 
            t_verify_aux (init_thread_state tid) tl);
    assert (thread_state itsl tid == 
            t_verify_step (t_verify_aux (init_thread_state tid) tl') v);
    let filter_fn = iskey #(key_type eac_sm) (partn_fn eac_sm) k in 
    assert (vl'_k == filter filter_fn vl');
    assert (vl_k == filter filter_fn vl);    
    let _ = 
      if key_of v <> k 
      then ( 
        lemma_filter_extend1 filter_fn vl;
        assert (vl'_k == vl_k)
      )
      else (
        lemma_filter_extend2 filter_fn vl;
        assert (vl_k == Seq.snoc vl'_k ve);
        assert (m.eacs k == seq_machine_run (seq_machine_of eac_sm) vl_k);
        lemma_reduce_append EACInit (trans_fn (seq_machine_of eac_sm)) vl'_k ve;
        assert (m.eacs k == eac_add ve (m'.eacs k))
      )
    in
    assert (forall (tid':valid_tid itsl).
             tid <> tid' ==>
             thread_log (I.s_seq itsl) tid' ==
             thread_log (I.s_seq (I.prefix itsl i)) tid')    
#pop-options

(* when the eac state of a key is "instore" then there is always a previous add *)
let lemma_eac_state_active_implies_prev_add (itsl: eac_log) (k:key{is_eac_state_active itsl k})
  : Lemma (ensures (has_some_add_of_key itsl k))
  = let rec aux (itsl:eac_log)
                (k:key)
      : Lemma (ensures is_eac_state_active itsl k ==> 
                       (exists (i:I.seq_index itsl). is_add_of_key k (I.index itsl i)))
              (decreases (I.length itsl))
      = if I.length itsl = 0
        then run_monitor_empty itsl k 
        else (
          aux (I.prefix itsl (I.length itsl - 1)) k;
          run_monitor_step itsl k
        )
    in
    aux itsl k;
    lemma_exists_sat_elems_exists (is_add_of_key k) (I.i_seq itsl)

#push-options "--query_stats --fuel 0,0 --ifuel 1,1"

(* the converse of the previous, eac state init implies no previous add *)
let lemma_eac_state_init_no_entry (itsl: eac_log) (k:key)
  : Lemma (requires (is_eac_state_init itsl k))
          (ensures (not (has_some_entry_of_key itsl k)))
  = let vl = vlog_ext_of_its_log itsl in
    let eacs = eac_state_of_key itsl k in
    let filter_fn = iskey #(key_type eac_sm) (partn_fn eac_sm) k in
    assert (eacs == EACInit);
    let vl' : seq vlog_entry_ext = partn eac_sm k vl in
    assert (forall (j:SA.seq_index vl').{:pattern (Seq.index vl' j)}
              filter_fn (Seq.index vl' j));
    assert (eacs == seq_machine_run (seq_machine_of eac_sm) vl');
    let rec aux (i:nat{i <= Seq.length vl'})
                (eacs:eac_state{eacs == seq_machine_run (seq_machine_of eac_sm) (SA.prefix vl' i) /\
                                ((eacs == EACInit /\ (forall (j:SA.seq_index vl'). j < i ==> not (filter_fn (Seq.index vl' j)))) \/
                                 (eacs <> EACInit))})
      : Lemma (ensures (Seq.equal vl' Seq.empty))
              (decreases (Seq.length vl' - i))
      = if i = Seq.length vl'
        then (
          if eacs <> EACInit
          then (
            assert (Seq.equal (SA.prefix vl' i) vl');
            false_elim()
          )
          else (
            assert (forall (j:SA.seq_index vl'). filter_fn (Seq.index vl' j) /\ not (filter_fn (Seq.index vl' j)));
            assert (Seq.length vl' = 0)
          )
        )
        else (
          let ve = Seq.index vl' i in
          let eacs' = eac_add ve eacs in
          assert (eacs' <> EACInit);
          assert (SA.prefix vl' (i + 1) `Seq.equal` (Seq.snoc (SA.prefix vl' i) ve));
          lemma_reduce_append EACInit (trans_fn (seq_machine_of eac_sm)) (SA.prefix vl' i) ve;
          assert (seq_machine_run (seq_machine_of eac_sm) (SA.prefix vl' (i + 1)) ==
                  eacs');
          aux (i + 1) eacs'
        )
    in
    assert (SA.prefix vl' 0 `Seq.equal` Seq.empty);
    lemma_reduce_empty EACInit (trans_fn (seq_machine_of eac_sm));
    aux 0 EACInit;
    assert (Seq.equal vl' Seq.empty);
    filter_all_not filter_fn vl;
    assert (forall (i:SA.seq_index vl). not (filter_fn (Seq.index vl i)));
    let aux (i:I.seq_index itsl)
      : Lemma (ensures (not (is_entry_of_key k (Seq.index (I.i_seq itsl) i))))
              [SMTPat (Seq.index (I.i_seq itsl) i)]
      = assert (Seq.index vl i == mk_vlog_entry_ext itsl i)
    in
    assert (forall (i:I.seq_index itsl). not (is_entry_of_key k (Seq.index (I.i_seq itsl) i)))

(* add method of an eac state *)
let rec lemma_eac_state_addm' (itsl: eac_log) 
                              (k:key{is_eac_state_instore itsl k})
                              (i:I.seq_index itsl)
  : Lemma 
    (requires (
      let v = I.index itsl i in
      is_add_of_key k v /\
      (forall (j:I.seq_index itsl). i < j ==> not (is_add_of_key k (I.index itsl j)))))
    (ensures (
      let v = I.index itsl i in
      E.add_method_of (eac_state_of_key itsl k) = 
      V.addm_of_entry (I.index itsl i)))
    (decreases (I.length itsl))
  = let l = I.length itsl in
    run_monitor_step itsl k;
    let itsl' = I.prefix itsl (l - 1) in
    let m = run_monitor itsl in
    let m' = run_monitor itsl' in
    assert (eac_state_of_key itsl k == m.eacs k);
    let v = I.index itsl (l - 1) in
    let ve = mk_vlog_entry_ext itsl (l - 1) in
    if i = l - 1 
    then ()
    else lemma_eac_state_addm' itsl' k i

let lemma_eac_state_addm (itsl: eac_log) (k:key{is_eac_state_instore itsl k})
  : Lemma (E.add_method_of (eac_state_of_key itsl k) = 
           V.addm_of_entry (I.index itsl (last_add_idx itsl k)))
  = let i = last_add_idx itsl k in
    SA.last_index_opt_elim (is_add_of_key k) (I.i_seq itsl);
    lemma_eac_state_addm' itsl k (last_add_idx itsl k)

(* the evicted value is always of the correct type for the associated key *)
let lemma_eac_value_correct_type (itsl: eac_log) (k:key)
  :  Lemma (requires (E.is_eac_state_active (eac_state_of_key itsl k)))
           (ensures is_value_of k (E.value_of (eac_state_of_key itsl k)))
  = let vl = vlog_ext_of_its_log itsl in
    let eacs = eac_state_of_key itsl k in
    let filter_fn = iskey #(key_type eac_sm) (partn_fn eac_sm) k in
    let vl' : seq vlog_entry_ext = partn eac_sm k vl in
    assert (forall (j:SA.seq_index vl').{:pattern (Seq.index vl' j)} filter_fn (Seq.index vl' j));
    assert (eacs == seq_machine_run (seq_machine_of eac_sm) vl');
    assert (eacs <> EACInit && eacs <> EACFail);
    let rec aux (i:nat{i <= Seq.length vl'})
                (eacs':eac_state{eacs' == seq_machine_run (seq_machine_of eac_sm) (SA.prefix vl' i) /\
                                (E.is_eac_state_active eacs' ==>
                                 is_value_of k (E.value_of eacs'))})
      : Lemma (ensures is_value_of k (E.value_of eacs))
              (decreases (Seq.length vl' - i))
      = if i = Seq.length vl' 
        then (
          assert (Seq.equal (SA.prefix vl' i) vl')
        )
        else (
          let ve = Seq.index vl' i in
          let eacs'' = eac_add ve eacs' in
          assert (SA.prefix vl' (i + 1) `Seq.equal` (Seq.snoc (SA.prefix vl' i) ve));
          lemma_reduce_append EACInit (trans_fn (seq_machine_of eac_sm)) (SA.prefix vl' i) ve;
          assert (seq_machine_run (seq_machine_of eac_sm) (SA.prefix vl' (i + 1)) ==
                  eacs'');
          aux (i + 1) eacs''
        )
    in
    assert (SA.prefix vl' 0 `Seq.equal` Seq.empty);
    lemma_reduce_empty EACInit (trans_fn (seq_machine_of eac_sm));
    aux 0 EACInit


#push-options "--ifuel 1,1 --fuel 1,1"
(* we never see operations on Root so its eac state is always init *)
let lemma_eac_state_of_root_init (itsl: eac_log)
  : Lemma (is_eac_state_init itsl Root)
  = let rec aux (itsl:eac_log)
                (m:monitored_state itsl)
      : Lemma (ensures  is_eac_state_init itsl Root)
              (decreases (I.length itsl))
      = if I.length itsl = 0
        then run_monitor_empty itsl Root
        else (
             let i = I.length itsl - 1 in
             let itsl' = I.prefix itsl i in
             let m' = run_monitor itsl' in
             let k = Root in
             aux itsl' m';
             run_monitor_step itsl Root
        )
    in
    aux itsl (run_monitor itsl)
#pop-options
#push-options "--ifuel 0,0 --fuel 1,1"

(* 
 * when the eac state of a key is Init (no operations on the key yet) no 
 * thread contains the key in its store. Valid only for non-root keys 
 * since we start off with the root in the cache of thread 0
 *)
let lemma_eac_state_init_store (itsl: eac_log) (k: key) (tid:valid_tid itsl)
  : Lemma (requires (k <> Root && is_eac_state_init itsl k))
          (ensures (not (store_contains (thread_store itsl tid) k)))
  = lemma_eac_state_init_no_entry itsl k;
    assert (not (has_some_entry_of_key itsl k));
    SA.lemma_exists_sat_elems_exists (is_entry_of_key k) (I.i_seq itsl);
    assert (forall (i:I.seq_index itsl). not (is_entry_of_key k (I.index itsl i)));
    let _, thread_log_tid = thread_log (s_seq itsl) tid in
    let aux (i:SA.seq_index thread_log_tid)
      : Lemma (not (is_entry_of_key k (Seq.index thread_log_tid i)))
              [SMTPat (Seq.index thread_log_tid i)]
      = assert (Seq.index thread_log_tid i ==
                Seq.index (I.i_seq itsl) (s2i_map itsl (tid, i)))
    in 
    assert (forall (i:SA.seq_index thread_log_tid). not (is_entry_of_key k (Seq.index thread_log_tid i)));
    let thread_state_tid = verify (tid, thread_log_tid) in
    let store_tid = Valid?.st thread_state_tid in
    let rec aux (i:nat{i <= Seq.length thread_log_tid})
                (ts:vtls{ ts == verify (tid, SA.prefix thread_log_tid i) /\
                          (Valid? ts ==> not (store_contains (Valid?.st ts) k)) })
      : Lemma (ensures not (store_contains store_tid k))
              (decreases (Seq.length thread_log_tid - i))
      = if i = Seq.length thread_log_tid
        then (
          assert (SA.prefix thread_log_tid i `Seq.equal` thread_log_tid)
        )
        else (
          let e = Seq.index thread_log_tid i in
          assert (not (is_entry_of_key k e));
          let ts' = t_verify_step ts e in
          assert (ts' == verify (tid, SA.prefix thread_log_tid (i +  1)));
          aux (i + 1) ts'
        )
    in
    assert (SA.prefix thread_log_tid 0 `Seq.equal` empty);
    aux 0 (init_thread_state tid)

#push-options "--ifuel 1,1 --fuel 1,1"
let t_verify_step_framing (v:vtls{Valid? v}) (e:vlog_entry) (k:key{key_of e <> k})
  : Lemma (let open Veritas.Verifier in
           let v' = t_verify_step v e in
           Valid? v' ==>
           store_contains (thread_store v') k == store_contains (thread_store v) k)
  = ()

let ancestor_key_of (e:vlog_entry) 
  : option key 
  = match e with
    | AddM _ k
    | EvictM _ k
    | EvictBM _ k _ -> Some k
    | _ -> None

let t_verify_step_framing_keys (v:vtls{Valid? v}) (e:vlog_entry) (k:key)
  : Lemma (let open Veritas.Verifier in
           let v' = t_verify_step v e in
           Valid? v' /\
           key_of e <> k /\
           ancestor_key_of e <> Some k ==>
           store_contains (thread_store v') k == store_contains (thread_store v) k /\
           Valid?.st v' k ==  Valid?.st v k
           )
  = ()

#pop-options


module VV = Veritas.Verifier
let key_in_unique_store (itsl: eac_log) (k:key) =
  let m = run_monitor itsl in
  forall (tid tid':valid_tid itsl). {:pattern (m.threads tid); (m.threads tid')}
    tid <> tid' /\
    store_contains (VV.thread_store (m.threads tid)) k ==>
    not (store_contains (VV.thread_store (m.threads tid')) k)

let elim_key_in_unique_store (itsl:eac_log) (k:key) (tid tid':valid_tid itsl)
  : Lemma 
    (requires key_in_unique_store itsl k /\
              tid <> tid' /\
              store_contains (VV.thread_store ((run_monitor itsl).threads tid)) k)
    (ensures  not (store_contains (VV.thread_store ((run_monitor itsl).threads tid')) k))
  = ()

let lemma_key_in_unique_store_step (itsl:eac_log{I.length itsl > 0})
                                   (k: key)
  : Lemma 
    (requires (
      let i = I.length itsl - 1 in
      let itsl' = I.prefix itsl i in
      let m' = run_monitor itsl' in
      key_in_unique_store itsl' k /\
      (forall (tid:valid_tid itsl).
           (EACEvictedBlum? (m'.eacs k) \/ EACEvictedMerkle? (m'.eacs k)) ==>
           not (store_contains (Valid?.st (m'.threads tid)) k))))
    (ensures
      key_in_unique_store itsl k)
  = run_monitor_step itsl k;
    let evicted eacs = (EACEvictedBlum? eacs || EACEvictedMerkle? eacs) in
    let i = I.length itsl - 1 in
    let itsl' = I.prefix itsl i in
    let m' = run_monitor itsl' in
    let m = run_monitor itsl in
    let v = I.index itsl i in
    let ve = mk_vlog_entry_ext itsl i in
    assert (v == to_vlog_entry ve); 
    let vl' = vlog_ext_of_its_log itsl' in
    let vl'_k = partn eac_sm k vl' in
    let vl = vlog_ext_of_its_log itsl in
    let vl_k = partn eac_sm k vl in
    assert (vl `Seq.equal` Seq.snoc vl' ve);
    let tid = thread_id_of itsl i in
    let _, tl' = thread_log (I.s_seq (I.prefix itsl i)) tid in
    let _, tl = thread_log (I.s_seq itsl) tid in
    assert (tl `Seq.equal` Seq.snoc tl' v);
    assert (SA.prefix tl (Seq.length tl - 1) `Seq.equal` tl');
    assert (m'.threads tid == verify (tid, tl'));
    assert (m.threads tid == t_verify_step (m'.threads tid) v);
    let st' = VV.thread_store (m'.threads tid) in
    let st =  VV.thread_store (m.threads tid) in
    let tid_unchanged (tid':valid_tid itsl)
      : Lemma 
        (requires tid' <> tid)
        (ensures m.threads tid' == m'.threads tid')
      = ()
    in
    let aux (tid0 tid1:valid_tid itsl)
      : Lemma 
        (requires 
          tid0 <> tid1 /\
          store_contains (VV.thread_store (m.threads tid0)) k)
        (ensures
          not (store_contains (VV.thread_store (m.threads tid1)) k))
        [SMTPat (m.threads tid0);
         SMTPat (m.threads tid1)]
      = if tid0 <> tid
        then (
          tid_unchanged tid0;
          assert (store_contains (VV.thread_store (m'.threads tid0)) k);
          assert (not (store_contains (VV.thread_store (m'.threads tid1)) k));          
          if tid1 <> tid
          then tid_unchanged tid1
          else (
            if key_of v <> k
            then (
              assert (vl'_k == vl_k);
              assert (m.eacs k == m'.eacs k);
              t_verify_step_framing (m'.threads tid1) v k
            )
            else (
              assert (vl_k == Seq.snoc vl'_k ve);
              assert (m.eacs k == eac_add ve (m'.eacs k));
              match ve with
              | EvictMerkle _ _
              | EvictBlum _ _ _
              | NEvict (Get _ _)
              | NEvict (Put _ _) ->
                //requires k to be in the store of tid1
                false_elim ()
              | NEvict (AddM r k') -> 
                assert (m.threads tid1 == t_verify_step (m'.threads tid1) (AddM r k'));
                assert (m'.eacs k == EACInit \/
                        EACEvictedMerkle? (m'.eacs k));
                if EACEvictedMerkle? (m'.eacs k)
                then false_elim() //it can't be in tid0
                else lemma_eac_state_init_store (I.prefix itsl i) k tid0
              | NEvict (AddB _ _ _) -> 
                false_elim()
            )
          )
        )
        else (
          tid_unchanged tid1;
          if key_of v <> k
          then (
              assert (vl'_k == vl_k);
              assert (m.eacs k == m'.eacs k);
              t_verify_step_framing (m'.threads tid0) v k
          )
          else (             
            assert (vl_k == Seq.snoc vl'_k ve);
            assert (m.eacs k == eac_add ve (m'.eacs k));
            match ve with
            | EvictMerkle _ _
            | EvictBlum _ _ _ ->
              //removes k, contradicts that k is m
              false_elim ()
            | NEvict (Get _ _)
            | NEvict (Put _ _) -> 
              //doesn't change k
              ()
            | NEvict (AddM r k') ->
              if EACEvictedMerkle? (m'.eacs k)
              then () //it's definitely not in tid1
              else lemma_eac_state_init_store (I.prefix itsl i) k tid1
            | NEvict (AddB _ _ _) ->
              //evicted, so nowhere initially
              ()
          )
        )
    in
    ()
                  

           

#push-options "--ifuel 1,1 --fuel 1,1 --z3rlimit_factor 6"
(* when the eac state of a key is evicted then no thread contains the key in its store *)
let lemma_unique_store_key (itsl: eac_log) 
                           (k: key) 
                           (tid:valid_tid itsl)
 : Lemma (key_in_unique_store itsl k /\
         (is_eac_state_evicted itsl k ==>
           not (store_contains (thread_store itsl tid) k)))
 = lemma_eac_state_of_root_init itsl;
   assert (is_eac_state_evicted itsl k ==> k <> Root);
   let evicted eacs = (EACEvictedBlum? eacs || EACEvictedMerkle? eacs) in
   let filter_fn = iskey #(key_type eac_sm) (partn_fn eac_sm) k in 
   let rec aux (itsl:eac_log)
               (m:monitored_state itsl)
     : Lemma (ensures 
                (forall (tid:valid_tid itsl). 
                   evicted (m.eacs k) ==>
                   not (store_contains (Valid?.st (m.threads tid)) k)) /\
                key_in_unique_store itsl k)
             (decreases (I.length itsl))
     = if I.length itsl = 0
       then (
         let vl = vlog_ext_of_its_log itsl in
         assert (vl `Seq.equal` empty);
         let vl' = partn eac_sm k vl in
         lemma_filter_empty filter_fn;
         assert (vl' `Seq.equal` empty);
         lemma_reduce_empty EACInit (trans_fn (seq_machine_of eac_sm));
         assert (m.eacs k == EACInit);
         assert (Seq.equal (I.i_seq itsl) empty);
         Veritas.Interleave.interleave_empty (IL?.prf itsl);
         assert (forall (tid:valid_tid itsl). Seq.index (I.s_seq itsl) tid `Seq.equal` empty);
         assert (key_in_unique_store itsl k)
       )
       else (
         run_monitor_step itsl k;
         let i = I.length itsl - 1 in
         let itsl' = I.prefix itsl i in
         let m' = run_monitor itsl' in
         aux itsl' m'; 
         assert (forall (tid:valid_tid itsl).
                   evicted (m'.eacs k) ==>
                   not (store_contains (Valid?.st (m'.threads tid)) k));
         assert (key_in_unique_store (I.prefix itsl i) k);
         let v = I.index itsl i in
         let ve = mk_vlog_entry_ext itsl i in
         let vl' = vlog_ext_of_its_log itsl' in
         let vl'_k = partn eac_sm k vl' in
         let vl = vlog_ext_of_its_log itsl in
         let vl_k = partn eac_sm k vl in
         assert (vl `Seq.equal` Seq.snoc vl' ve);
         let tid = thread_id_of itsl i in
         let _, tl' = thread_log (I.s_seq (I.prefix itsl i)) tid in
         let _, tl = thread_log (I.s_seq itsl) tid in
         assert (tl `Seq.equal` Seq.snoc tl' v);
         assert (SA.prefix tl (Seq.length tl - 1) `Seq.equal` tl');
         assert (m'.threads tid == verify (tid, tl'));
         assert (m.threads tid == t_verify_step (m'.threads tid) v);
         let st' = Valid?.st (m'.threads tid) in
         let st =  Valid?.st (m.threads tid) in
         let rec aux (tid':valid_tid itsl)
           : Lemma 
               (requires evicted (m.eacs k))
               (ensures not (store_contains (Valid?.st (m.threads tid')) k))
               [SMTPat (m.threads tid')]
           = if tid' = tid
             then (
               if key_of v <> k 
               then (
                 assert (vl'_k == vl_k);
                 assert (m.eacs k == m'.eacs k);               
                 t_verify_step_framing (m'.threads tid') v k;
                 assert (evicted (m'.eacs k));
                 assert (not (store_contains (Valid?.st (m'.threads tid')) k));
                 assert (store_contains st k == store_contains st' k);
                 assert (not (store_contains st' k))
               ) 
               else (
                 assert (vl_k == Seq.snoc vl'_k ve);
                 assert (m.eacs k == eac_add ve (m'.eacs k));
                 //has to be an evict, since we end in an evict state
                 match ve with
                 | EvictMerkle (EvictM _ k') vv ->
                   assert (v == EvictM k k');
                   assert (store_contains (VV.thread_store (m'.threads tid')) k);
                   assert (not (store_contains (VV.thread_store (m.threads tid')) k))
                 | EvictBlum _ _ _ -> ()
                 | _ -> false_elim()
               )
             )
             else (
                  assert (thread_log (I.s_seq itsl) tid' ==
                          thread_log (I.s_seq (I.prefix itsl i)) tid');
                  assert (m.threads tid' == m'.threads tid');
                  if key_of v <> k
                  then (
                        assert (vl'_k == vl_k);
                        assert (m.eacs k == m'.eacs k))
                  else (
                    assert (vl_k == Seq.snoc vl'_k ve);
                    assert (m.eacs k == eac_add ve (m'.eacs k));
                    match ve with
                    | EvictMerkle (EvictM _ _) _
                    | EvictBlum _ _ _ ->
                      assert (store_contains (VV.thread_store (m'.threads tid)) k);
                      elim_key_in_unique_store (I.prefix itsl i) k tid tid';
                      assert (not (store_contains (VV.thread_store (m'.threads tid')) k))
                    | _ -> false_elim()
                  )
             )
         in
         lemma_key_in_unique_store_step itsl k;
         assert (key_in_unique_store itsl k);           
         ()
       )
   in
   let m = run_monitor itsl in
   aux itsl m
#pop-options 

let lemma_eac_state_evicted_store itsl k tid = 
    lemma_unique_store_key itsl k tid


let lemma_key_in_unique_store2 (itsl: eac_log) (k:key) (tid1 tid2: valid_tid itsl):
  Lemma (requires (tid1 <> tid2))
        (ensures (not (store_contains (thread_store itsl tid1) k &&
                       store_contains (thread_store itsl tid2) k)))
  = lemma_unique_store_key itsl k tid1;
    assert (key_in_unique_store itsl k);
    if store_contains (thread_store itsl tid1) k
    && store_contains (thread_store itsl tid2) k
    then (
      let m = run_monitor itsl in
      assert (thread_store itsl tid1 ==
              VV.thread_store (m.threads tid1));
      assert (thread_store itsl tid2 ==
              VV.thread_store (m.threads tid2));
      assert (store_contains (VV.thread_store (m.threads tid1)) k);
      elim_key_in_unique_store itsl k tid1 tid1
    )

let data_key_not_root (k:data_key) 
  : Lemma (k <> Root)
  = ()

let proper_desc_not_root (k:key) (k1:key{is_proper_desc k k1}) 
  : Lemma (k <> Root)
  = ()

#push-options "--ifuel 1,1 --fuel 0,0 --z3rlimit_factor 8"

(* when the eac_state of k is instore, then k is in the store of a unique verifier thread *)
let rec stored_tid_aux (itsl: eac_log) 
                       (k:key)
  : Tot (tid_opt:option (valid_tid itsl)
         {
           match tid_opt with
           | None -> 
             (k <> Root \/ thread_count itsl = 0) /\
             not (is_eac_state_instore itsl k) /\
             (forall tid.{:pattern (thread_store itsl tid)}  
               not (store_contains (thread_store itsl tid) k))
           | Some tid ->
             let tstore = thread_store itsl tid in            
             store_contains tstore k  /\
             (if k=Root 
              then (
                tid == 0 /\
                eac_state_of_key itsl k == EACInit
              )
              else (
               is_eac_state_instore itsl k /\
               E.add_method_of (eac_state_of_key itsl k) 
                 == V.add_method_of tstore k /\
               (is_data_key k ==>
                 eac_state_value itsl k == V.stored_value tstore k)
               )
              )
         })
        (decreases (I.length itsl))
  = if I.length itsl = 0
    then (
      run_monitor_empty itsl k;
      if k = Root && thread_count itsl > 0
      then (
        Some 0 
      )
      else ( 
        None
      )
    )
    else (
      run_monitor_step itsl k;
      let i = I.length itsl - 1 in
      let itsl' = I.prefix itsl i in
      let m' = run_monitor itsl' in
      let m = run_monitor itsl in
      let v = I.index itsl i in
      let ve = mk_vlog_entry_ext itsl i in
      let vl' = vlog_ext_of_its_log itsl' in
      let vl'_k = partn eac_sm k vl' in
      let vl = vlog_ext_of_its_log itsl in
      let vl_k = partn eac_sm k vl in
      let tid = thread_id_of itsl i in
      let _, tl' = thread_log (I.s_seq (I.prefix itsl i)) tid in
      let _, tl = thread_log (I.s_seq itsl) tid in
      let tid_opt' = stored_tid_aux itsl' k in
      let ts = thread_state itsl tid in
      let tstore = thread_store itsl tid in
      let ts' = thread_state itsl' tid in
      let tstore' = thread_store itsl' tid in      
      assert (ts == t_verify_step ts' v);
      if EACInStore? (m.eacs k)
      then (
        if key_of v = k
        then (
          assert (m.eacs k == eac_add ve (m'.eacs k));
          match v with
          | Get _ _
          | Put _ _ ->
            assert (E.add_method_of (m.eacs k) ==
                    E.add_method_of (m'.eacs k));
            assert (V.add_method_of tstore k ==
                    V.add_method_of tstore' k);
            let Some tid' = tid_opt' in 
            if tid' = tid 
            then ( Some tid )
            else (
              assert (is_data_key k);
              data_key_not_root k;
              assert (k <> Root);
              assert (store_contains tstore' k);
              assert (store_contains (thread_store itsl' tid') k);
              lemma_key_in_unique_store2 itsl' k tid tid';
              false_elim()
            )
          | AddM (k0, value) k' ->
            assert (k0 == k);
            proper_desc_not_root k0 k';
            assert (k <> Root);
            let EACInStore MAdd value' = m.eacs k in
            assert (value' == value);
            let Some r = tstore k in
            Some tid
          | AddB _ _ _ ->
            lemma_eac_state_of_root_init itsl;
            assert (k <> Root);          
            Some tid
        )
        else (
          let Some s_tid = tid_opt' in
          let tstore' = thread_store itsl' s_tid in
          assert (m.eacs k == m'.eacs k);
          if tid = s_tid
          then (
            match v with
            | Get _ _ -> 
              Some tid
            | Put _ _  -> 
              Some tid
            | _ ->
              t_verify_step_framing_keys ts' v k;            
              Some tid
          )
          else Some s_tid
        )
      )
      else (
        if key_of v = k
        then (
          assert (m.eacs k == eac_add ve (m'.eacs k));
          match v with
          | Get _ _
          | Put _ _
          | AddM _ _
          | AddB _ _ _ -> None
          | _ ->
            FStar.Classical.forall_intro (lemma_eac_state_evicted_store itsl k);
            None
        )
        else (
          t_verify_step_framing_keys ts' v k;
          assert (m.eacs k == m'.eacs k);
          match tid_opt' with
          | None -> 
            assert (forall tid.{:pattern thread_store itsl' tid}
                   not (store_contains (thread_store itsl' tid) k));
            let aux (tid0:valid_tid itsl) 
              : Lemma 
                (ensures (not (store_contains (thread_store itsl tid0) k)))
                [SMTPat (thread_store itsl tid0)]
              = if tid0 <> tid
                then (assert (thread_log (I.s_seq itsl) tid0 ==
                              thread_log (I.s_seq itsl') tid0);
                      assert (thread_state itsl tid0 ==
                              thread_state itsl' tid0);
                      assert (thread_store itsl' tid0 ==                               
                              Valid?.st (thread_state itsl' tid0)))
                else ()
            in
            None
          | Some tid' -> 
            if k = Root
            then Some 0
            else (
              assert (store_contains (thread_store itsl' tid') k);
              None
            )
        )
      )
    )

#pop-options

let stored_tid (itsl: eac_log) 
               (k:key{is_eac_state_instore itsl k})
  : Tot (tid: valid_tid itsl{store_contains (thread_store itsl tid) k})
  = let Some tid = stored_tid_aux itsl k in
    tid

(* uniqueness: k is not in any store other than stored_tid *)
let lemma_key_in_unique_store (itsl: eac_log) (k:key) (tid: valid_tid itsl):
  Lemma (requires (is_eac_state_instore itsl k))
        (ensures (tid <> stored_tid itsl k ==> not (store_contains (thread_store itsl tid) k)))
  = let s_tid = stored_tid itsl k in
    assert (store_contains (thread_store itsl s_tid) k);
    if store_contains (thread_store itsl tid) k
    && tid <> s_tid
    then lemma_key_in_unique_store2 itsl k s_tid tid
    else ()


(* for data keys, the value in the store is the same as the value associated with the eac state *)
let lemma_eac_stored_value (itsl: eac_log) (k: data_key{is_eac_state_instore itsl k})
  : Lemma (eac_state_value itsl k = stored_value itsl k)
  = let Some tid = stored_tid_aux itsl k in ()

(* 
 * for all keys, the add method stored in the store is the same as the add method associated 
 * with eac state
 *)
let lemma_eac_stored_addm (itsl: eac_log) (k:key{is_eac_state_instore itsl k})
  : Lemma (E.add_method_of (eac_state_of_key itsl k) = stored_add_method itsl k)
  = let Some tid = stored_tid_aux itsl k in ()

(* if k is in a verifier store, then its eac_state is instore *)
let lemma_instore_implies_eac_state_instore (itsl:eac_log) (k:key{k <> Root}) (tid:valid_tid itsl)
  : Lemma (store_contains (thread_store itsl tid) k ==> is_eac_state_instore itsl k)
  = let _ = stored_tid_aux itsl k in ()
         
(* the root is always in thread 0 *)
let lemma_root_in_store0 (itsl: eac_log{thread_count itsl > 0})
  : Lemma (store_contains (thread_store itsl 0) Root) 
  = let _ = stored_tid_aux itsl Root in ()

let lemma_root_not_in_store (itsl: eac_log) (tid:valid_tid itsl{tid > 0})
  : Lemma (not (store_contains (thread_store itsl tid) Root))
  = lemma_root_in_store0 itsl;
    lemma_key_in_unique_store2 itsl Root 0 tid

#push-options "--ifuel 1,1"
(* we use eac constraints to associate a value with each key *)
let eac_value_aux (itsl: eac_log) (k:key)
  : value
  = let m = run_monitor itsl in
    match m.eacs k with
    | EACFail -> false_elim()
    | EACInit -> 
      if k = Root && thread_count itsl > 0
      then (
        let _ = stored_tid_aux itsl k in
        V.stored_value (Valid?.st (m.threads 0)) Root
      )
      else init_value k
    | EACInStore _ _ -> stored_value itsl k
    | EACEvictedBlum v _ _ -> v
    | EACEvictedMerkle v -> v

#push-options "--ifuel 1,1 --fuel 0,0 --z3rlimit_factor 4"
let lemma_eac_value_aux_typing (itsl:eac_log) (k:key)
  : Lemma (is_value_of k (eac_value_aux itsl k))
  = let rec aux (itsl:eac_log)
      : Lemma (ensures 
                 is_value_of k (eac_value_aux itsl k) /\
                 (is_eac_state_instore itsl k ==> is_value_of k (eac_state_value itsl k)))
              (decreases (I.length itsl))
      = if I.length itsl = 0
        then (
          run_monitor_empty itsl k
        )
        else (
          let i = I.length itsl - 1 in
          let itsl' = I.prefix itsl i in
          aux itsl';
          run_monitor_step itsl k;
          let m = run_monitor itsl in
          match m.eacs k with
          | EACEvictedBlum _ _ _
          | EACEvictedMerkle _ -> ()
          | EACInStore _ _ -> ()
          | EACInit -> 
            assert (thread_count itsl > 0)
        )
    in
    aux itsl
#pop-options

let eac_value itsl k 
  = lemma_eac_value_aux_typing itsl k;
    eac_value_aux itsl k
  
(* eac_value is consistent with stored value *)
let lemma_eac_value_is_stored_value (itsl: eac_log) (k:key) (tid: valid_tid itsl):  
  Lemma (requires (store_contains (thread_store itsl tid) k))
        (ensures (eac_value itsl k = V.stored_value (thread_store itsl tid) k))
  = let Some tid' = stored_tid_aux itsl k in
    if tid = tid' 
    then (
      if k <> Root 
      then ()
      else ()
    ) 
    else (
      lemma_key_in_unique_store2 itsl k tid tid'
    )

let lemma_eac_value_is_evicted_value (itsl: eac_log) (k:key)
  : Lemma (requires (is_eac_state_evicted itsl k))
          (ensures (eac_state_evicted_value itsl k = eac_value itsl k))
  = ()        
#restart-solver
#push-options "--z3rlimit_factor 4"
let lemma_ext_evict_val_is_stored_val (itsl: its_log) (i: I.seq_index itsl)
  : Lemma (requires (is_evict (I.index itsl i)))
          (ensures (store_contains (thread_store (I.prefix itsl i) (thread_id_of itsl i)) (key_at itsl i) /\
                    is_evict_ext (vlog_entry_ext_at itsl i) /\
                    V.stored_value (thread_store (I.prefix itsl i) (thread_id_of itsl i)) (key_at itsl i) = 
                    value_ext (vlog_entry_ext_at itsl i)))
  = let rec aux (itsl:its_log{I.length itsl > 0})
      : Lemma (ensures (
                let i = I.length itsl - 1 in 
                is_evict (I.index itsl i) ==>
                store_contains (thread_store (I.prefix itsl i) (thread_id_of itsl i)) (key_at itsl i) /\
                is_evict_ext (vlog_entry_ext_at itsl i) /\
                V.stored_value (thread_store (I.prefix itsl i) (thread_id_of itsl i)) (key_at itsl i) == 
                value_ext (vlog_entry_ext_at itsl i)))
       = let i = I.length itsl - 1 in
         let itsl' = I.prefix itsl i in       
         let m' = run_monitor itsl' in
         let m = run_monitor itsl in
         let v = I.index itsl i in
         let ve = mk_vlog_entry_ext itsl i in
         let vl' = vlog_ext_of_its_log itsl' in
         let k = key_at itsl i in
         let vl'_k = partn eac_sm k vl' in
         let vl = vlog_ext_of_its_log itsl in
         let vl_k = partn eac_sm k vl in
         let tid = thread_id_of itsl i in
         let _, tl' = thread_log (I.s_seq (I.prefix itsl i)) tid in
         let _, tl = thread_log (I.s_seq itsl) tid in
         run_monitor_step itsl k;
         if i = 0
         then run_monitor_empty itsl' (key_at itsl i)
         else ()
    in
    let itsl' = I.prefix itsl (i + 1) in
    I.lemma_prefix_index itsl (i + 1) i    ;
    aux itsl';
    I.lemma_prefix_prefix itsl (i + 1) i;
    I.lemma_i2s_map_prefix itsl (i + 1) i
#pop-options    
  
#push-options "--fuel 0,0 --z3rlimit_factor 4"
        

let evict_is_evicted (itsl:eac_log{I.length itsl > 0})
  : Lemma (let i = I.length itsl - 1 in
           let v = I.index itsl i in
           let m = run_monitor itsl in
           let eacs = m.eacs (key_of v) in
           is_evict v ==> EACEvictedBlum? eacs \/ EACEvictedMerkle? eacs)
  = let i = I.length itsl - 1 in
    let v = I.index itsl i in
    run_monitor_step itsl (key_of v)

(* if an evict is not the last entry of a key, then there is a add subsequent to the 
 * evict *)
let lemma_evict_has_next_add (itsl: its_log) 
                             (i:I.seq_index itsl)
                             (j:nat { i < j /\ j <= I.length itsl })
  : Lemma 
    (requires 
      is_evict (I.index itsl i) /\
      is_eac (I.prefix itsl j) /\         
      exists_sat_elems (is_entry_of_key (key_of (I.index itsl i))) (I.i_seq itsl) /\
      i < last_idx_of_key itsl (key_of (I.index itsl i)))
    (ensures (has_next_add_of_key itsl i (key_of (I.index itsl i))))
  = let itsl_j = I.prefix itsl j in
    let itsl_i = I.prefix itsl (i + 1) in
    I.lemma_prefix_prefix itsl j (i + 1);
    lemma_eac_implies_prefix_eac itsl_j (i + 1);
    assert (is_eac itsl_i);
    let v = I.index itsl i in
    let is_eac_evicted = function
      | EACEvictedBlum _ _ _
      | EACEvictedMerkle _ -> true
      | _ -> false
    in
    let rec aux (k:nat{i < k /\
                     k <= I.length itsl /\
                     (forall (k':I.seq_index itsl). i < k' /\ k' < k ==> key_of (I.index itsl k') <> key_of v)})
      : Lemma 
        (requires k <= last_idx_of_key itsl (key_of v) /\
                  (let m' = run_monitor (I.prefix itsl k) in
                   (forall (tid:valid_tid itsl).{:pattern (m'.threads tid)} not (store_contains (VV.thread_store (m'.threads tid)) (key_of v)))
                   ))
        (ensures has_next_add_of_key itsl i (key_of v))
        (decreases (I.length itsl - k))
      = if k = I.length itsl 
        then false_elim()
        else (
          let itsl_k = I.prefix itsl k in
          let itsl_k_1 = I.prefix itsl (k + 1) in          
          I.lemma_prefix_prefix itsl (k + 1) k;
          let m' = run_monitor itsl_k in
          let m = run_monitor itsl_k_1 in
          run_monitor_step itsl_k_1 (key_of v);
          assert (I.prefix itsl_k_1 k == itsl_k);
          assert (I.length itsl_k_1 = k + 1);
          let tid = thread_id_of itsl_k_1 k in
          let v' = I.index itsl_k_1 k in
          assert (m.threads tid ==
                  t_verify_step (m'.threads tid) v');
          if key_of v = key_of v' 
          then (
            match v' with
            | AddM _ _ 
            | AddB _ _ _ ->
              intro_has_next (is_add_of_key (key_of v)) (I.i_seq itsl) i k
            | _ ->
              assert (~(Valid? (m.threads tid)))
          )
          else (t_verify_step_framing (thread_state itsl_k tid) v' (key_of v);
                assert (store_contains (VV.thread_store (m.threads tid)) (key_of v) ==
                        store_contains (VV.thread_store (m'.threads tid)) (key_of v));
                assert (not (store_contains (VV.thread_store (m.threads tid)) (key_of v)));
                assert (forall (tid':valid_tid itsl_k_1). tid' <> tid ==> m.threads tid' == m'.threads tid');
                aux (k + 1))
        )
    in
    let m = run_monitor itsl_i in
    I.lemma_prefix_index itsl (i + 1) i;
    evict_is_evicted itsl_i;
    assert (is_eac_evicted (m.eacs (key_of v)));
    assert (is_eac_state_evicted itsl_i (key_of v));
    let aux2 (tid:valid_tid itsl)
      : Lemma (not (store_contains (VV.thread_store (m.threads tid)) (key_of v)))
              [SMTPat (m.threads tid)]
      = lemma_unique_store_key itsl_i (key_of v) tid
    in
    aux (i + 1)

#push-options "--ifuel 1,1 --fuel 1,1"
let lemma_root_never_evicted (itsl: its_log) (i:I.seq_index itsl)
  : Lemma (requires (is_evict (I.index itsl i)))
          (ensures (V.key_of (I.index itsl i) <> Root))
  = let itsl' = I.prefix itsl (i + 1) in
    run_monitor_step itsl' Root
#pop-options    

#push-options "--fuel 0,0 --ifuel 0,0"
(* since the itsl is sorted by clock, the following lemma holds *)
let lemma_clock_ordering (itsl: its_log) (i1 i2: I.seq_index itsl):
  Lemma (requires (clock itsl i1 `ts_lt` clock itsl i2))
        (ensures (i1 < i2))
  = assert (clock_sorted itsl);
    if i2 <= i1
    then assert (clock itsl i2 `ts_leq` clock itsl i1)
#pop-options

(* the state of each key for an empty log is init *)
let lemma_init_state_empty (itsl: its_log {I.length itsl = 0}) (k: key)
  : Lemma (eac_state_of_key itsl k = EACInit)
  = assert (Seq.equal (vlog_ext_of_its_log itsl) empty);
    SA.lemma_reduce_empty EACInit (trans_fn (seq_machine_of eac_sm));
    assert (eac_state_of_key itsl k == 
            seq_machine_run (seq_machine_of eac_sm)
                            (partn eac_sm k empty));
    lemma_filter_is_proj (iskey #(key_type eac_sm) (partn_fn eac_sm) k) empty;
    lemma_proj_length (partn eac_sm k empty) empty;
    assert (Seq.equal (partn eac_sm k empty) empty)
