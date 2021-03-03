module Veritas.Intermediate.Global

let verifiable_implies_prefix_verifiable
  (#vcfg:_) (gl:verifiable_log vcfg) (i:nat{i <= S.length gl}):
  Lemma (ensures (verifiable #vcfg (SA.prefix gl i))) = 
  let pgl = SA.prefix gl i in
  let aux (tid: SA.seq_index pgl):
    Lemma (ensures (IntT.verifiable (thread_log pgl tid)))
          [SMTPat (IntT.verifiable (thread_log pgl tid))] =
    assert(thread_log pgl tid = thread_log gl tid);          
    () 
  in
  ()

let rec add_seq_aux (#vcfg:_) (gl: verifiable_log vcfg): 
  Tot (seq (ms_hashfn_dom))
  (decreases (S.length gl)) = 
  let p = S.length gl in
  if p = 0 then S.empty #(ms_hashfn_dom)
  else
    let gl' = SA.prefix gl (p - 1) in
    // verifiable_implies_prefix_verifiable gl (p - 1);
    append (add_seq_aux gl') (IntT.blum_add_seq (thread_log gl (p - 1)))

let add_seq (#vcfg:_) (gl: verifiable_log vcfg): seq (ms_hashfn_dom) = 
  add_seq_aux gl

let rec lemma_g_hadd_correct_aux #vcfg (gl: verifiable_log vcfg):
  Lemma (ensures (hadd gl = ms_hashfn (add_seq gl)))
        (decreases (S.length gl)) = 
  let p = S.length gl in
  let s = add_seq gl in
  let h = hadd gl in
  if p = 0 then
    lemma_hashfn_empty()
  else (
    let gl' = SA.prefix gl (p - 1) in
    let s' = add_seq gl' in
    let h' = hadd gl' in
    lemma_g_hadd_correct_aux gl';
    assert(h' = ms_hashfn s');

    let tl = thread_log gl (p - 1) in
    let st = blum_add_seq tl in
    let ht = IntT.hadd tl in
    IntT.lemma_hadd_correct tl;
    lemma_hashfn_agg s' st
  )

let lemma_g_hadd_correct (#vcfg:_) (gl: verifiable_log vcfg):
  Lemma (ensures (hadd gl = ms_hashfn (add_seq gl))) = 
  lemma_g_hadd_correct_aux gl


#push-options "--z3rlimit_factor 3"

let rec add_set_map_aux #vcfg (gl: verifiable_log vcfg) (ii: sseq_index gl {is_blum_add (indexss gl ii)}):
  Tot (j: SA.seq_index (add_seq gl){S.index (add_seq gl) j = blum_add_elem (indexss gl ii)})
  (decreases (S.length gl))  
  = 
  let (tid, i) = ii in
  let p = S.length gl in
  let gl' = SA.prefix gl (p - 1) in
  let s' = add_seq gl' in
  let tl = thread_log gl (p - 1) in

  if tid = p - 1 then
    S.length s' + (IntT.add_seq_map tl i)
  else
    add_set_map_aux gl' ii  

#pop-options

(* mapping from blum_add entries in verifier log to the index in add seq *)
let add_set_map (#vcfg:_) (gl: verifiable_log vcfg) (ii: sseq_index gl {is_blum_add (indexss gl ii)}):
  (j: SA.seq_index (add_seq gl){S.index (add_seq gl) j = blum_add_elem (indexss gl ii)}) = 
  add_set_map_aux gl ii

let rec add_set_map_inv_aux (#vcfg:_) (gl: verifiable_log vcfg) (j: SA.seq_index (add_seq gl)):
  Tot (ii: sseq_index gl {is_blum_add (indexss gl ii) /\ 
                      add_set_map gl ii = j})
  (decreases (S.length gl)) = 
  let p = S.length gl in
  let gl' = SA.prefix gl (p - 1) in
  let s' = add_seq gl' in
  let tl = thread_log gl (p - 1) in

  if j < S.length s' then
    add_set_map_inv_aux gl' j
  else
    let j' = j - S.length s' in
    let i = IntT.add_seq_inv_map tl j' in
    (p - 1, i)

(* inverse mapping from add_seq to the blum add entries in the verifier logs *)
let add_set_map_inv (#vcfg:_) (gl: verifiable_log vcfg) (j: SA.seq_index (add_seq gl)):
  (ii: sseq_index gl {is_blum_add (indexss gl ii) /\ 
                      add_set_map gl ii = j}) = add_set_map_inv_aux gl j

let rec lemma_add_set_map_inv_aux (#vcfg:_) (gl: verifiable_log vcfg) (ii: sseq_index gl {is_blum_add (indexss gl ii)}):
  Lemma (ensures (add_set_map_inv gl (add_set_map gl ii) = ii))
        (decreases (S.length gl)) = 
  let (tid, i) = ii in
  let p = S.length gl in
  let gl' = SA.prefix gl (p - 1) in
  let s' = add_seq gl' in
  let tl = thread_log gl (p - 1) in

  if tid = p - 1 then ()
  else
    lemma_add_set_map_inv_aux gl' ii

let lemma_add_set_map_inv (#vcfg:_) (gl: verifiable_log vcfg) (ii: sseq_index gl {is_blum_add (indexss gl ii)}):
  Lemma (ensures (add_set_map_inv gl (add_set_map gl ii) = ii)) = lemma_add_set_map_inv_aux gl ii

(* a single sequence containing all the blum evicts *)
let rec evict_seq_aux (#vcfg:_) (gl: verifiable_log vcfg): 
  Tot (seq ms_hashfn_dom)
  (decreases (S.length gl)) =
  let p = S.length gl in
  if p = 0 then S.empty #(ms_hashfn_dom)
  else
    let gl' = SA.prefix gl (p - 1) in
    append (evict_seq_aux gl') (IntT.blum_evict_seq (thread_log gl (p - 1)))

(* a single sequence containing all the blum evicts *)
let evict_seq (#vcfg:_) (gl: verifiable_log vcfg): seq ms_hashfn_dom = 
  evict_seq_aux gl

let rec lemma_ghevict_correct_aux (#vcfg:_) (gl: verifiable_log vcfg):
  Lemma (ensures (hevict gl = ms_hashfn (evict_seq gl)))
        (decreases (S.length gl)) = 
  let p = S.length gl in
  let s = evict_seq gl in
  let h = hevict gl in
  if p = 0 then
    lemma_hashfn_empty()
  else (
    let gl' = SA.prefix gl (p - 1) in
    let s' = evict_seq gl' in
    let h' = hevict gl' in
    lemma_ghevict_correct_aux gl';
    let tl = thread_log gl (p - 1) in
    let st = IntT.blum_evict_seq tl in
    let ht = IntT.hevict tl in
    IntT.lemma_hevict_correct tl;
    
    lemma_hashfn_agg s' st
  )
        
let lemma_ghevict_correct (#vcfg:_) (gl: verifiable_log vcfg):
  Lemma (ensures (hevict gl = ms_hashfn (evict_seq gl))) =
  lemma_ghevict_correct_aux gl

(* two indexes of a sequence s are different *)
let diff_elem (#a:eqtype) (s:seq a) (i1: SA.seq_index s) (i2: SA.seq_index s) = 
  S.index s i1 <> S.index s i2

let uniq_prop (#a:eqtype) (s: seq a) =
  forall (i1: SA.seq_index s). 
  forall (i2: SA.seq_index s).
  {:pattern diff_elem s i1 i2}
  i1 <> i2 ==> diff_elem s i1 i2

(* for some reason, fstar is unable to assert (diff_elem s i1 i2) for uniq_prop s without 
 * this lemma *)
let lemma_uniq_idx (#a:eqtype) (s: seq a) (i1 i2: SA.seq_index s):
  Lemma (requires (uniq_prop s /\ i1 <> i2)) 
        (ensures (diff_elem s i1 i2))
        [SMTPat (diff_elem s i1 i2)] = () 

let lemma_uniq_prop_tail (#a:eqtype) (s: seq a{S.length s > 0}):
  Lemma (requires (uniq_prop s))
        (ensures (uniq_prop (S.tail s))) = 
  let s' = tail s in
  let aux (i1 i2: SA.seq_index s'):
    Lemma (ensures (i1 <> i2 ==> diff_elem s' i1 i2))
          [SMTPat (diff_elem s' i1 i2)] = 
    
    assert(S.index s (1 + i1) = S.index s' i1);          
    assert(S.index s (1 + i2) = S.index s' i2);
    if i1 = i2 then ()
    else (
      assert(diff_elem s' i1 i2 = diff_elem s (1 + i1) (1 + i2));
      ()
    )
  in
  ()

let some_elem (#a:eqtype) (s: seq a) (x: a{count x s >= 1}): 
  Tot (i:SA.seq_index s{S.index s i = x}) = index_mem x s  

let rec lemma_count_len (#a:eqtype) (s: seq a) (x: a):
  Lemma (ensures (count x s <= S.length s)) 
        (decreases (S.length s))
        = 
  let n = S.length s in
  if n = 0 then ()
  else 
    lemma_count_len (tail s) x

let rec lemma_uniq_prop_counts (#a:eqtype) (s: seq a) (x: a):
  Lemma (requires (uniq_prop s))
        (ensures (count x s <= 1)) 
        (decreases (S.length s)) = 
  let n = S.length s in
  if n <= 1 then lemma_count_len s x
  else if count x s <= 1 then ()
  else (
    assert(uniq_prop s);
    let h = head s in
    let s' = tail s in

    if h = x then (
      assert(count x s' >= 1);
      let i2 = some_elem s' x in
      assert(S.index s (1 + i2) = x);
      assert(diff_elem s 0 (1 + i2));
      ()
    )
    else (
      assert(count x s = count x s');
      lemma_uniq_prop_tail s;
      lemma_uniq_prop_counts s' x
    )
  )

module MH = Veritas.MultiSetHash

let rec lemma_evict_elem_tids #vcfg (gl: verifiable_log vcfg) (i: SA.seq_index (evict_seq gl))
  : Lemma (ensures (let es = evict_seq gl in
                    MH.thread_id_of (S.index es i) < S.length gl))
          (decreases (S.length gl)) = 
  let p = S.length gl in
  let es = evict_seq gl in
  if p = 0 then ()
  else
    let gl' = SA.prefix gl (p - 1) in
    let es' = evict_seq gl' in
    if i < S.length es' then
      lemma_evict_elem_tids gl' i
    else      
      IntT.lemma_evict_elem_tid (thread_log gl (p - 1))

let rec lemma_evict_elem_unique_aux #vcfg (gl: verifiable_log vcfg) (i1 i2: SA.seq_index (evict_seq gl))
  : Lemma (requires (i1 < i2))
          (ensures (diff_elem (evict_seq gl) i1 i2))
          (decreases (S.length gl)) = 
  let p = S.length gl in
  let es = evict_seq gl in
  if p = 0 then ()
  else
    let gl' = SA.prefix gl (p - 1) in
    let es' = evict_seq gl' in
    let tl = thread_log gl (p - 1) in
    let et = IntT.blum_evict_seq tl in
    if i1 < S.length es' then
      if i2 < S.length es' then
        lemma_evict_elem_unique_aux gl' i1 i2
      else (
        lemma_evict_elem_tids gl' i1; 
        IntT.lemma_evict_elem_tid tl
      )
    else
      IntT.lemma_evict_elem_unique tl (i1 - S.length es') (i2 - S.length es')

let lemma_evict_elem_unique #vcfg (gl: verifiable_log vcfg) (i1 i2: SA.seq_index (evict_seq gl))
  : Lemma (requires (i1 <> i2))
          (ensures (diff_elem (evict_seq gl) i1 i2))
          [SMTPat (diff_elem (evict_seq gl) i1 i2)] = 
  if i1 < i2 then
    lemma_evict_elem_unique_aux gl i1 i2
  else
    lemma_evict_elem_unique_aux gl i2 i1

let lemma_evict_elem_unique2 #vcfg (gl: verifiable_log vcfg):
  Lemma (uniq_prop (evict_seq gl)) = ()

let lemma_evict_elem_count #vcfg (gl: verifiable_log vcfg) (x: ms_hashfn_dom)
  : Lemma (count x (evict_seq gl) <= 1) =
  lemma_evict_elem_unique2 gl;
  lemma_uniq_prop_counts (evict_seq gl) x


module MS = Veritas.MultiSet

(* the global evict set is a set (not a multiset) *)
let evict_set_is_set (#vcfg:_) (gl: verifiable_log vcfg): 
  Lemma (ensures (is_set (evict_set gl))) = 
  let es = evict_set gl in
  let aux (x:ms_hashfn_dom):
    Lemma (ensures (MS.mem x es <= 1))
          [SMTPat (MS.mem x es)] = 
      lemma_evict_elem_count gl x;
      seq2mset_mem #_ #ms_hashfn_dom_cmp (evict_seq gl) x
  in
  ()

#push-options "--z3rlimit_factor 6"

let rec evict_seq_map_aux (#vcfg:_) (gl: verifiable_log vcfg) (ii: sseq_index gl {is_evict_to_blum (indexss gl ii)}):
  Tot (j: SA.seq_index (evict_seq gl) {S.index (evict_seq gl) j = blum_evict_elem gl ii})
  (decreases (S.length gl)) = 
  let (tid, i) = ii in
  let p = S.length gl in
  let gl' = SA.prefix gl (p - 1) in
  let s' = evict_seq gl' in
  let s = evict_seq gl in
  let tl = thread_log gl (p - 1) in
  let et = IntT.blum_evict_seq tl in
  if tid = p - 1 then (
    //S.length s' + IntT.evict_seq_map tl i
    assert(s == append s' et);
    assert(S.length s = S.length s' + S.length et);
    let i' = IntT.evict_seq_map tl i in
    assert(i' < S.length et);
    let j = S.length s' + i' in
    assert(j < S.length s);
    //assert(S.index s j = blum_evict_elem gl ii);
    assert(blum_evict_elem gl ii = IntT.blum_evict_elem tl i);
    assert(IntT.blum_evict_elem tl i = S.index et i');
    assert(S.index s j = S.index et i');
    j
  )
  else
    evict_seq_map_aux gl' ii

#pop-options

let evict_seq_map (#vcfg:_) (gl: verifiable_log vcfg) (ii: sseq_index gl {is_evict_to_blum (indexss gl ii)}):
  (j: SA.seq_index (evict_seq gl) {S.index (evict_seq gl) j = 
                                 blum_evict_elem gl ii}) = evict_seq_map_aux gl ii

#push-options "--z3rlimit_factor 3"

let rec evict_seq_map_inv_aux (#vcfg:_) (gl: verifiable_log vcfg) (j: SA.seq_index (evict_seq gl)):
  Tot (ii: sseq_index gl {is_evict_to_blum (indexss gl ii) /\
                      blum_evict_elem gl ii = S.index (evict_seq gl) j /\
                      evict_seq_map gl ii = j}) 
  (decreases (S.length gl)) = 
  let p = S.length gl in
  let gl' = SA.prefix gl (p - 1) in
  let s' = evict_seq gl' in
  let s = evict_seq gl in
  let tl = thread_log gl (p - 1) in
  let et = IntT.blum_evict_seq tl in
  if j < S.length s' then
    evict_seq_map_inv_aux gl' j
  else
    let j' = j - S.length s' in
    let i = IntT.evict_seq_inv_map tl j' in
    let ii = (p - 1, i) in
    assert(s == append s' et);
    assert(S.index s j = S.index et j');
    (p-1, i)

#pop-options

let evict_seq_map_inv (#vcfg:_) (gl: verifiable_log vcfg) (j: SA.seq_index (evict_seq gl)):
  (ii: sseq_index gl {is_evict_to_blum (indexss gl ii) /\
                      blum_evict_elem gl ii = S.index (evict_seq gl) j /\
                      evict_seq_map gl ii = j}) = evict_seq_map_inv_aux gl j

let rec lemma_evict_seq_inv_aux (#vcfg:_) (gl: verifiable_log vcfg) (ii: sseq_index gl {is_evict_to_blum (indexss gl ii)}):
  Lemma (ensures (evict_seq_map_inv gl (evict_seq_map gl ii) = ii)) 
        (decreases (S.length gl)) = 
  let (tid, i) = ii in
  let p = S.length gl in
  let gl' = SA.prefix gl (p - 1) in
  let s' = evict_seq gl' in
  let tl = thread_log gl (p - 1) in
  if tid = p - 1 then ()
  else
    lemma_evict_seq_inv_aux gl' ii

let lemma_evict_seq_inv (#vcfg:_) (gl: verifiable_log vcfg) (ii: sseq_index gl {is_evict_to_blum (indexss gl ii)}):
  Lemma (requires True)
        (ensures (evict_seq_map_inv gl (evict_seq_map gl ii) = ii)) = lemma_evict_seq_inv_aux gl ii
