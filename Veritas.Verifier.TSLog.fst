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

assume
val mapi (#a #b:_) (s:seq a) (f:(seq_index s -> b))
  : t:seq b{
    Seq.length s == Seq.length t /\
    (forall (i:seq_index s). Seq.index t i == f i)
   }

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

#push-options "--z3rlimit_factor 4"
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
(* is this an evict add consistent log *)
let is_eac (itsl: its_log):bool = admit()

let eac_boundary (itsl: neac_log):
  (i:I.seq_index itsl{is_eac (I.prefix itsl i) &&
                      not (is_eac (I.prefix itsl (i + 1)))})
  = admit()
  
(* if itsl is eac, then any prefix is also eac *)
let lemma_eac_implies_prefix_eac (itsl: eac_log) (i:nat {i <= I.length itsl}):
  Lemma (requires True)
        (ensures (is_eac (I.prefix itsl i)))
    = admit()
  
(* if the ts log is eac, then its state ops are read-write consistent *)
let lemma_eac_implies_state_ops_rw_consistent (itsl: eac_log):
  Lemma (rw_consistent (state_ops itsl))
  = admit()
  
(* the eac state of a key at the end of an its log *)
let eac_state_of_key (itsl: its_log) (k:key): eac_state 
  = admit()

let lemma_eac_state_of_key_valid (itsl: eac_log) (k:key):
  Lemma (EACFail <> eac_state_of_key itsl k)
  = admit()

(* the extended vlog entry to use for eac checking *)
let vlog_entry_ext_at (itsl: its_log) (i:I.seq_index itsl): 
  (e:vlog_entry_ext{E.to_vlog_entry e = I.index itsl i})
  = admit()

(* the eac state transition induced by the i'th entry *)
let lemma_eac_state_transition (itsl: its_log) (i:I.seq_index itsl):
  Lemma (eac_state_post itsl i = 
         eac_add (vlog_entry_ext_at itsl i) (eac_state_pre itsl i))
  = admit()         

(* if the ith entry does not involve key k, the eac state of k is unchanged *)
let lemma_eac_state_same (itsl: its_log) (i: I.seq_index itsl) (k: key):
  Lemma (requires (key_at itsl i <> k))
        (ensures (eac_state_of_key (I.prefix itsl i) k == 
                  eac_state_of_key (I.prefix itsl (i + 1)) k))
  = admit()

let lemma_eac_boundary_state_transition (itsl: neac_log):
  Lemma (requires True)
        (ensures (eac_add (vlog_entry_ext_at itsl (eac_boundary itsl))
                          (eac_boundary_state_pre itsl) = EACFail))
        [SMTPat (eac_boundary itsl)]
  = admit()


(* when the eac state of a key is "instore" then there is always a previous add *)
let lemma_eac_state_active_implies_prev_add (itsl: eac_log) 
  (k:key{is_eac_state_active itsl k}):
  Lemma (requires True)
        (ensures (has_some_add_of_key itsl k))
  //      [SMTPat (is_eac_state_instore itsl k)]
  = admit()
  
(* the converse of the previous, eac state init implies no previous add *)
let lemma_eac_state_init_no_entry (itsl: eac_log) (k:key):
  Lemma (requires (is_eac_state_init itsl k))
        (ensures (not (has_some_entry_of_key itsl k)))
 = admit()
 
(* add method of an eac state *)
let lemma_eac_state_addm (itsl: eac_log) (k:key{is_eac_state_instore itsl k}):
  Lemma (E.add_method_of (eac_state_of_key itsl k) = 
         V.addm_of_entry (I.index itsl (last_add_idx itsl k)))
 = admit()
 
(* the evicted value is always of the correct type for the associated key *)
let lemma_eac_value_correct_type (itsl: eac_log) (k:key):  
  Lemma (requires (E.is_eac_state_active (eac_state_of_key itsl k)))
        (ensures is_value_of k (E.value_of (eac_state_of_key itsl k)))
 = admit()


(* we never see operations on Root so its eac state is always init *)
let lemma_eac_state_of_root_init (itsl: eac_log):
  Lemma (is_eac_state_init itsl Root)
 = admit()
 
(* 
 * when the eac state of a key is Init (no operations on the key yet) no 
 * thread contains the key in its store. Valid only for non-root keys 
 * since we start off with the root in the cache of thread 0
 *)
let lemma_eac_state_init_store (itsl: eac_log) (k: key) (tid:valid_tid itsl):
  Lemma (requires (k <> Root && is_eac_state_init itsl k))
        (ensures (not (store_contains (thread_store itsl tid) k)))
 = admit()


(* when the eac state of a key is evicted then no thread contains the key in its store *)
let lemma_eac_state_evicted_store  (itsl: eac_log) (k: key{is_eac_state_evicted itsl k}) 
  (tid:valid_tid itsl):
  Lemma (not (store_contains (thread_store itsl tid) k))
 = admit()


(* when the eac_state of k is instore, then k is in the store of a unique verifier thread *)
let stored_tid (itsl: eac_log) (k:key{is_eac_state_instore itsl k}): 
  (tid: valid_tid itsl{store_contains (thread_store itsl tid) k})
 = admit()


(* uniqueness: k is not in any store other than stored_tid *)
let lemma_key_in_unique_store (itsl: eac_log) (k:key) (tid: valid_tid itsl):
  Lemma (requires (is_eac_state_instore itsl k))
        (ensures (tid <> stored_tid itsl k ==> not (store_contains (thread_store itsl tid) k)))
  = admit()         

let lemma_key_in_unique_store2 (itsl: eac_log) (k:key) (tid1 tid2: valid_tid itsl):
  Lemma (requires (tid1 <> tid2))
        (ensures (not (store_contains (thread_store itsl tid1) k &&
                       store_contains (thread_store itsl tid2) k)))
  = admit()

(* for data keys, the value in the store is the same as the value associated with the eac state *)
let lemma_eac_stored_value (itsl: eac_log) (k: data_key{is_eac_state_instore itsl k}):
  Lemma (eac_state_value itsl k = stored_value itsl k)
  = admit()


(* 
 * for all keys, the add method stored in the store is the same as the add method associated 
 * with eac state
 *)
let lemma_eac_stored_addm (itsl: eac_log) (k:key{is_eac_state_instore itsl k}):
  Lemma (E.add_method_of (eac_state_of_key itsl k) = stored_add_method itsl k)
  = admit()


(* if k is in a verifier store, then its eac_state is instore *)
let lemma_instore_implies_eac_state_instore (itsl:eac_log) (k:key{k <> Root}) (tid:valid_tid itsl):
  Lemma (store_contains (thread_store itsl tid) k ==> is_eac_state_instore itsl k)
  = admit()
         
(* the root is always in thread 0 *)
let lemma_root_in_store0 (itsl: eac_log{thread_count itsl > 0}):
  Lemma (store_contains (thread_store itsl 0) Root) = admit()

let lemma_root_not_in_store (itsl: eac_log) (tid:valid_tid itsl{tid > 0}):
  Lemma (not (store_contains (thread_store itsl tid) Root)) = admit()
  
(* we use eac constraints to associate a value with each key *)
let eac_value (itsl: eac_log) (k:key): value_type_of k = admit()

(* eac_value is consistent with stored value *)
let lemma_eac_value_is_stored_value (itsl: eac_log) (k:key) (tid: valid_tid itsl):  
  Lemma (requires (store_contains (thread_store itsl tid) k))
        (ensures (eac_value itsl k = V.stored_value (thread_store itsl tid) k))
  = admit()        

let lemma_eac_value_is_evicted_value (itsl: eac_log) (k:key):
  Lemma (requires (is_eac_state_evicted itsl k))
        (ensures (eac_state_evicted_value itsl k = eac_value itsl k))
  = admit()        

let lemma_ext_evict_val_is_stored_val (itsl: its_log) (i: I.seq_index itsl):
  Lemma (requires (is_evict (I.index itsl i)))
        (ensures (store_contains (thread_store (I.prefix itsl i) (thread_id_of itsl i)) (key_at itsl i) /\
                  is_evict_ext (vlog_entry_ext_at itsl i) /\
                  V.stored_value (thread_store (I.prefix itsl i) (thread_id_of itsl i)) (key_at itsl i) = 
                  value_ext (vlog_entry_ext_at itsl i)))
  = admit()        

(* if an evict is not the last entry of a key, then there is a add subsequent to the 
 * evict *)
let lemma_evict_has_next_add (itsl: its_log) (i:I.seq_index itsl):
  Lemma (requires (is_evict (I.index itsl i) /\
                   exists_sat_elems (is_entry_of_key (key_of (I.index itsl i))) (I.i_seq itsl)) /\
                   i < last_idx_of_key itsl (key_of (I.index itsl i)))
        (ensures (has_next_add_of_key itsl i (key_of (I.index itsl i))))
  = admit()        

let lemma_root_never_evicted (itsl: its_log) (i:I.seq_index itsl):
  Lemma (requires (is_evict (I.index itsl i)))
        (ensures (V.key_of (I.index itsl i) <> Root))
  = admit()        

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
let lemma_init_state_empty (itsl: its_log {I.length itsl = 0}) (k: key):
  Lemma (eac_state_of_key itsl k = EACInit)
  = admit()        

(* broken ... but lots of useful stuff below *)

// // let lemma_verifier_thread_state_extend (#p:pos) (itsl: its_log p) (i:seq_index itsl):
// //   Lemma (thread_state (prefix itsl (i + 1)) (thread_id_of itsl i)== 
// //          t_verify_step (thread_state (prefix itsl i) (thread_id_of itsl i))
// //                        (vlog_entry_at itsl i)) = 
// //   let gl = partition_idx_seq itsl in                       
// //   let tid = thread_id_of itsl i in                       
  
//   admit()                       

// (* extended time sequence log (with evict values) 
// let rec time_seq_ext_aux (#p:pos) (itsl: its_log p):
//   Tot (le:vlog_ext{project_seq itsl = to_vlog le})
//   (decreases (length itsl)) =*)
//   (*
//   let m = length itsl in
//   if m = 0 then (
//     lemma_empty itsl;
//     lemma_empty (project_seq itsl);
//     let r = empty #vlog_entry_ext in
//     lemma_empty (to_vlog r);
//     r
//   )
//   else (
//     let (e,id) = telem itsl in

//     (* recurse *)
//     let itsl' = its_prefix itsl (m - 1) in
//     let r' = time_seq_ext_aux itsl' in

//     (* project seq of itsl and itsl' differ by log entry e *)
//     lemma_project_seq_extend itsl;
//     assert(project_seq itsl = append1 (project_seq itsl') e);

//     (* log entries of verifier thread id *)
//     let gl = partition_idx_seq itsl in
//     let l = index gl id in
//     assert(snd (index (g_tid_vlog gl) id) = l);

//     (* since l is verifiable, the value at last position is well-defined *)
//     assert(VT.verifiable (id, l));
//     (* prove length l > 0 *)
//     lemma_partition_idx_extend1 itsl;

//     if is_evict_to_merkle e then (
//       let v = evict_value (id, l) (length l - 1) in
//       let r = append1 r' (EvictMerkle e v) in
//       lemma_prefix1_append r' (EvictMerkle e v);
//       lemma_map_extend to_vlog_entry r;
//       r
//     )
//     else if is_evict_to_blum e then (
//       let v = evict_value (id, l) (length l - 1) in
//       let r = append1 r' (EvictBlum e v id) in
//       lemma_prefix1_append r' (EvictBlum e v id);
//       lemma_map_extend to_vlog_entry r;
//       r
//     )
//     else (
//       let r = append1 r' (NEvict e) in
//       lemma_prefix1_append r' (NEvict e);
//       lemma_map_extend to_vlog_entry r;
//       r
//     )
//   )
//   *)


// let rec lemma_its_prefix_ext (#n:pos) (itsl:its_log n) (i:nat{i <= length itsl}):
//   Lemma (requires True)
//         (ensures (time_seq_ext (its_prefix itsl i) = prefix (time_seq_ext itsl) i)) 
//         (decreases (length itsl)) = 
//   let n = length itsl in          
//   if i = n then ()
//   else (
//     assert(n > 0 && i < n);

//     if i = n - 1 then
//       admit()
//     else

//     admit()
//   )

// (* if itsl is eac, then any prefix is also eac *)
// let lemma_eac_implies_prefix_eac (#p:pos) (itsl: eac_ts_log p) (i:nat {i <= length itsl}):
//   Lemma (requires True)
//         (ensures (is_eac_log (its_prefix itsl i)))
//         [SMTPat (its_prefix itsl i)] = admit()

// (* 
//  * when the eac state of a key is Init (no operations on the key yet) no 
//  * thread contains the key in its store 
//  *)
// let lemma_eac_state_init_store 
//    (#p:pos) 
//    (itsl: eac_ts_log p) (k: key{k <> Root && is_eac_state_init itsl k}) (id:nat{id < p}):
//    Lemma (not (store_contains (thread_store (verifier_thread_state itsl id)) k)) 
//    = admit()

// (* when the eac state of a key is EACEvicted then no thread contains the key in its store *)
// let lemma_eac_state_evicted_store (#p:pos) (itsl: eac_ts_log p) 
//   (k: key{is_eac_state_evicted itsl k}) (id:nat{id < p}):
//     Lemma (not (store_contains (thread_store (verifier_thread_state itsl id)) k)) = admit()

// (* when the eac state of a key is "instore" then there is always a previous add *)
// let lemma_eac_state_instore_implies_prev_add (#p:pos) (itsl: eac_ts_log p) (k:key{is_eac_state_instore itsl k}):
//   Lemma (has_some_add_of_key k (project_seq itsl)) = admit()

// (* if the eac_state of k is instore, then that k is in the store of the verifier thread of its last add *)
// let lemma_eac_state_instore (#p:pos) (itsl: eac_ts_log p) (k:key{is_eac_state_instore itsl k}):
//   Lemma (store_contains (thread_store (verifier_thread_state itsl (last_add_tid itsl k))) k /\
//          stored_value (thread_store (verifier_thread_state itsl (last_add_tid itsl k))) k = 
//          EACInStore?.v (eac_state_of_key itsl k)) = admit()

// let lemma_eac_state_instore_addm (#p:pos) (itsl: eac_ts_log p) (k:key{is_eac_state_instore itsl k}):
//   Lemma (is_add (index (project_seq itsl) (last_add_idx itsl k)) /\
//          store_contains (thread_store (verifier_thread_state itsl (last_add_tid itsl k))) k /\
//          EACInStore?.m (eac_state_of_key itsl k) = 
//          addm_of_entry (index (project_seq itsl) (last_add_idx itsl k)) /\
//          EACInStore?.m (eac_state_of_key itsl k) = 
//          add_method_of (thread_store (verifier_thread_state itsl (last_add_tid itsl k))) k) = admit()

// (* if the eac state of k is instore, then k is not in the store of any verifier thread other than 
//  * its last add thread *)
// let lemma_eac_state_instore2 (#p:pos) (itsl: eac_ts_log p) 
//   (k:key{is_eac_state_instore itsl k}) (id:nat{id < p}):
//   Lemma (requires (id <> last_add_tid itsl k))
//         (ensures (not (store_contains (thread_store (verifier_thread_state itsl id)) k))) = admit()

// let lemma_instore_implies_eac_state_instore (#p:pos) (itsl:eac_ts_log p) (k:key{k <> Root}) (tid:nat{tid < p}):
//   Lemma (store_contains (thread_store (verifier_thread_state itsl tid)) k ==> is_eac_state_instore itsl k) = 
//   admit()

// (* the root is always in thread 0 *)
// let lemma_root_in_store0 (#p:pos) (itsl: eac_ts_log p):
//   Lemma (store_contains (thread_store (verifier_thread_state itsl 0)) Root) = admit()

// let lemma_root_not_in_store (#p:pos) (itsl: eac_ts_log p) (tid:pos {tid < p}):
//   Lemma (not (store_contains (thread_store (verifier_thread_state itsl tid)) Root)) = admit()

// (* the evicted value is always of the correct type for the associated key *)
// let lemma_evict_value_correct_type (#p:pos) (itsl: eac_ts_log p) (k:key{is_eac_state_evicted itsl k}):
//   Lemma (is_value_of k (E.value_of (eac_state_of_key itsl k))) = admit()

// (* 
//  * for keys in a thread store, return the value in the thread store; 
//  * for other keys return the last evict value or null (init)
//  *)
// let eac_value (#n:pos) (itsl: eac_ts_log n) (k:key): value_type_of k = 
//   if k = Root then (
//     lemma_root_in_store0 itsl;
//     stored_value (thread_store (verifier_thread_state itsl 0)) Root
//   )
//   else 
//     let es = eac_state_of_key itsl k in
//     match es with
//     | EACInit -> init_value k 
//     | EACEvictedMerkle v -> lemma_evict_value_correct_type itsl k; v
//     | EACEvictedBlum v _ _ -> lemma_evict_value_correct_type itsl k; v
//     | EACInStore _ _ -> 
//       (* the store where the last add happened contains key k *)
//       let tid = last_add_tid itsl k in
//       let st = thread_store (verifier_thread_state itsl tid) in
        
//       lemma_eac_state_instore itsl k;
//       assert(store_contains st k);

//       stored_value st k

// let lemma_eac_value_is_stored_value (#p:pos) (itsl: eac_ts_log p) (k:key) (id:nat{id < p}):
//   Lemma (requires (store_contains (thread_store (verifier_thread_state itsl id)) k))
//         (ensures (eac_value itsl k = 
//                   stored_value (thread_store (verifier_thread_state itsl id)) k)) = admit()

// let lemma_eac_value_is_evicted_value (#p:pos) (itsl: eac_ts_log p) (k:key):
//   Lemma (requires (is_eac_state_evicted itsl k))
//         (ensures (eac_state_evicted_value itsl k = eac_value itsl k)) = admit()

// let lemma_ext_evict_val_is_stored_val (#p:pos) (itsl: its_log p) (i: seq_index itsl):
//   Lemma (requires (is_evict (fst (index itsl i))))
//         (ensures (is_evict_ext (index (time_seq_ext itsl) i) /\
//                   store_contains (thread_store (verifier_thread_state (its_prefix itsl i)
//                                                                       (snd (index itsl i))))
//                                  (V.key_of (fst (index itsl i))) /\
//                   value_ext (index (time_seq_ext itsl) i) = 
//                   stored_value (thread_store (verifier_thread_state (its_prefix itsl i)
//                                                                     (snd (index itsl i))))
//                                (V.key_of (fst (index itsl i))))) = admit()


// let lemma_evict_has_next_add (#p:pos) (itsl: its_log p) (i:seq_index itsl):
//   Lemma (requires (is_evict (index itsl i) /\
//                    exists_sat_elems (entry_of_key (key_of (index itsl i))) itsl) /\
//                    i < last_idx_of_key itsl (key_of (index itsl i)))
//         (ensures (has_next_add_of_key itsl i (key_of (index itsl i)))) = admit()
