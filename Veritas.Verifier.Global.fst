module Veritas.Verifier.Global

module MS = Veritas.MultiSet

let lemma_prefix_verifiable (gl: verifiable_log) (i:seq_index gl):
  Lemma (requires True)
        (ensures (verifiable (prefix gl i)))
        [SMTPat (prefix gl i)] = 
  let pgl = prefix gl i in
  let aux (tid:seq_index pgl):
    Lemma (requires True)
          (ensures (VT.verifiable (thread_log pgl tid)))
          [SMTPat (VT.verifiable (thread_log pgl tid))] = 
    assert(thread_log pgl tid = thread_log gl tid);
    ()
  in
  ()

let rec hadd_aux (gl: verifiable_log): 
  Tot (ms_hash_value)
  (decreases (length gl)) = 
  let p = length gl in
  if p = 0 then empty_hash_value
  else  (
    let gl' = prefix gl (p - 1) in
    lemma_prefix_verifiable gl (p - 1);
    let h1 = hadd_aux gl' in
    let h2 = VT.hadd (thread_log gl (p - 1)) in
    ms_hashfn_agg h1 h2
  )

(* aggregate hadd over all verifier threads *)
let hadd (gl: verifiable_log): ms_hash_value =
  hadd_aux gl

let rec hevict_aux (gl: verifiable_log): 
  Tot (ms_hash_value)
  (decreases (length gl)) = 
  let p = length gl in
  if p = 0 then empty_hash_value
  else  (
    let gl' = prefix gl (p - 1) in
    lemma_prefix_verifiable gl (p - 1);
    let h1 = hevict_aux gl' in
    let h2 = thread_hevict (VT.verify (thread_log gl (p - 1))) in
    ms_hashfn_agg h1 h2
  )

(* aggregate hadd over all verifier threads *)
let hevict (gl: verifiable_log): ms_hash_value =
  hevict_aux gl

let clock (gl: verifiable_log) (i: sseq_index gl): timestamp = 
  let (tid, idx) = i in  
  let tl = thread_log gl tid in
  VT.clock tl idx

(* global add sequence *)
let rec g_add_seq_aux (gl: verifiable_log): 
  Tot (seq (ms_hashfn_dom))
  (decreases (length gl)) = 
  let p = length gl in
  if p = 0 then empty #(ms_hashfn_dom)
  else (
    let gl' = prefix gl (p - 1) in
    lemma_prefix_verifiable gl (p - 1);
    append (g_add_seq_aux gl') (blum_add_seq (thread_log gl (p - 1)))
  )

(* global add sequence *)
let g_add_seq (gl: verifiable_log): seq (ms_hashfn_dom) = g_add_seq_aux gl

(* the hadd that the verifier computes is the multiset hash of all the adds *)
let rec lemma_g_hadd_correct_aux (gl: verifiable_log):
  Lemma (requires True)
        (ensures (hadd gl = ms_hashfn (g_add_seq gl)))
        (decreases (length gl)) = 
  let p = length gl in
  let s = g_add_seq gl in
  let h = hadd gl in
  
  if p = 0 then 
    lemma_hashfn_empty()
  
  else (
    let gl' = prefix gl (p - 1) in
    lemma_prefix_verifiable gl (p - 1);    
    let s' = g_add_seq gl' in
    let h' = hadd gl' in

    lemma_g_hadd_correct_aux gl';
    // assert(h' = ms_hashfn s');

    let tl = thread_log gl (p - 1) in
    let st = blum_add_seq tl in
    let ht = VT.hadd tl in
    lemma_hadd_correct tl;

    lemma_hashfn_agg s' st
  )

(* the hadd that the verifier computes is the multiset hash of all the adds *)
let lemma_g_hadd_correct (gl: verifiable_log):
  Lemma (hadd gl = ms_hashfn (g_add_seq gl)) =
  lemma_g_hadd_correct_aux gl

let rec add_set_map_aux (gl: verifiable_log) (ii: sseq_index gl {is_blum_add (indexss gl ii)}):
  Tot (j: seq_index (g_add_seq gl){index (g_add_seq gl) j = blum_add_elem (indexss gl ii)}) 
  (decreases (length gl)) =
  let (tid,i) = ii in
  let p = length gl in
  let gl' = prefix gl (p - 1) in
  let s' = g_add_seq gl' in
  let tl = thread_log gl (p - 1) in

  if tid = p - 1 then
    length s' + (VT.add_seq_map tl i)  
  else
    add_set_map_aux gl' ii
  
let add_set_map (gl: verifiable_log) (ii: sseq_index gl {is_blum_add (indexss gl ii)}):
  (j: seq_index (g_add_seq gl){index (g_add_seq gl) j = blum_add_elem (indexss gl ii)}) = 
  add_set_map_aux gl ii

(* inverse mapping from add_seq to the blum add entries in the verifier logs *)
let rec add_set_map_inv_aux (gl: verifiable_log) (j: seq_index (g_add_seq gl)):
  Tot (ii: sseq_index gl {is_blum_add (indexss gl ii) /\ add_set_map gl ii = j})
  (decreases (length gl)) = 
  let p = length gl in
  let gl' = prefix gl (p - 1) in
  let s' = g_add_seq gl' in
  let tl = thread_log gl (p - 1) in  
  let s = g_add_seq gl in

  if j < length s' then 
    add_set_map_inv_aux gl' j  
  else 
    let j' = j - length s' in
    let i = VT.add_seq_inv_map tl j' in
    (p-1, i)  

(* inverse mapping from add_seq to the blum add entries in the verifier logs *)
let add_set_map_inv (gl: verifiable_log) (j: seq_index (g_add_seq gl)):
  (ii: sseq_index gl {is_blum_add (indexss gl ii) /\ 
                      add_set_map gl ii = j}) = 
  add_set_map_inv_aux gl j                      

let rec lemma_add_set_map_inv_aux (gl: verifiable_log)(ii: sseq_index gl {is_blum_add (indexss gl ii)}):
  Lemma (requires True)
        (ensures (add_set_map_inv gl (add_set_map gl ii) = ii))
        (decreases (length gl)) =
  let (tid,i) = ii in
  let p = length gl in
  let gl' = prefix gl (p - 1) in
  let s' = g_add_seq gl' in
  let tl = thread_log gl (p - 1) in

  if tid = p - 1 then ()
  else
    lemma_add_set_map_inv_aux gl' ii

let lemma_add_set_map_inv (gl: verifiable_log)(ii: sseq_index gl {is_blum_add (indexss gl ii)}):
  Lemma (requires True)
        (ensures (add_set_map_inv gl (add_set_map gl ii) = ii))
        [SMTPat (add_set_map gl ii)] = 
  lemma_add_set_map_inv_aux gl ii

let rec g_evict_seq_aux (gl: verifiable_log):
  Tot (seq (ms_hashfn_dom))
  (decreases (length gl)) = 
  let p = length gl in
  if p = 0 then empty #(ms_hashfn_dom)
  else (
    let gl' = prefix gl (p - 1) in
    lemma_prefix_verifiable gl (p - 1);
    append (g_evict_seq_aux gl') (blum_evict_seq (thread_log gl (p - 1)))
  )

(* a single sequence containing all the blum evicts *)
let g_evict_seq (gl: verifiable_log): seq ms_hashfn_dom  = 
  g_evict_seq_aux gl

let rec lemma_ghevict_correct_aux (gl: verifiable_log):
  Lemma (requires True)
        (ensures (hevict gl = ms_hashfn (g_evict_seq gl)))
        (decreases (length gl)) = 
  let p = length gl in 
  let s = g_evict_seq gl in
  let h = hevict gl in

  if p = 0 then
    lemma_hashfn_empty()
  else (
    let gl' = prefix gl (p - 1) in
    lemma_prefix_verifiable gl (p - 1);
    let s' = g_evict_seq gl' in
    let h' = hevict gl' in

    lemma_ghevict_correct_aux gl';

    let tl = thread_log gl (p - 1) in
    let st = blum_evict_seq tl in
    let ht = VT.hevict tl in
    lemma_hevict_correct tl;
    
    lemma_hashfn_agg s' st
  )

let lemma_ghevict_correct (gl: verifiable_log):
  Lemma (hevict gl = ms_hashfn (g_evict_seq gl)) = 
  lemma_ghevict_correct_aux gl

(* two indexes of a sequence s are different *)
let diff_elem (#a:eqtype) (s:seq a) (i1: seq_index s) (i2: seq_index s{i1 <> i2}) = 
  index s i1 <> index s i2

(* for any two indexes, the elements at indexes are different *)
let uniq_prop (#a:eqtype) (s: seq a) = forall (i1: seq_index s). forall (i2: seq_index s{i1 <> i2}). 
  diff_elem s i1 i2

(* for some reason, fstar is unable to assert (diff_elem s i1 i2) for uniq_prop s without 
 * this lemma *)
let lemma_uniq_idx (#a:eqtype) (s: seq a) (i1 i2: seq_index s):
  Lemma (requires (uniq_prop s /\ i1 <> i2)) 
        (ensures (diff_elem s i1 i2))
        [SMTPat (diff_elem s i1 i2)] = () 

(* if s is uniq, then tail of s is also uniq *)
let lemma_uniq_prop_tail (#a:eqtype) (s: seq a{length s > 0}):
  Lemma (requires (uniq_prop s))
        (ensures (uniq_prop (tail s))) = 
  let s' = tail s in        
  let aux (i1 i2: seq_index s'):
    Lemma (requires (i1 <> i2))
          (ensures (diff_elem s' i1 i2))
          [SMTPat (diff_elem s' i1 i2)] = 
    (* needed *)
    assert(diff_elem s (1 + i1) (1 + i2));
    ()
  in
  ()

let some_elem (#a:eqtype) (s: seq a) (x: a{count x s >= 1}): 
  Tot (i:seq_index s{index s i = x}) = index_mem x s  

let rec lemma_count_len (#a:eqtype) (s: seq a) (x: a):
  Lemma (requires True)
        (ensures (count x s <= length s)) 
        (decreases (length s))
        = 
  let n = length s in
  if n = 0 then ()
  else 
    lemma_count_len (tail s) x

let rec lemma_uniq_prop_counts (#a:eqtype) (s: seq a) (x: a):
  Lemma (requires (uniq_prop s))
        (ensures (count x s <= 1)) 
        (decreases (length s)) = 
  let n = length s in
  if n <= 1 then lemma_count_len s x
  else if count x s <= 1 then ()
  else (
    assert(uniq_prop s);
    let h = head s in
    let s' = tail s in

    if h = x then (
      assert(count x s' >= 1);
      let i2 = some_elem s' x in
      assert(index s (1 + i2) = x);
      assert(not (diff_elem s 0 (1 + i2)));
      assert(diff_elem s 0 (1 + i2));
      ()
    )
    else (
      assert(count x s = count x s');
      lemma_uniq_prop_tail s;
      lemma_uniq_prop_counts s' x
    )
  )

let rec lemma_evict_elem_tids (gl: verifiable_log) (i: seq_index (g_evict_seq gl)):
  Lemma (requires True)
        (ensures (MH.thread_id_of (index (g_evict_seq gl) i) < length gl))
        (decreases (length gl)) = 
  let p = length gl in 
  let es = g_evict_seq gl in
  if p = 0 then ()
  else 
    let gl' = prefix gl (p - 1) in
    let es' = g_evict_seq gl' in

    if i < length es' then 
      lemma_evict_elem_tids gl' i  
    else 
      VT.lemma_evict_elem_tid (thread_log gl (p - 1))

let rec lemma_evict_elem_unique_aux (gl: verifiable_log) (i1 i2: seq_index (g_evict_seq gl)):
  Lemma (requires (i1 < i2))
        (ensures (diff_elem  (g_evict_seq gl) i1 i2))
        (decreases (length gl)) =
  let p = length gl in
  let es = g_evict_seq gl in
  if p = 0 then ()
  else (
    let gl' = prefix gl (p - 1) in
    let es' = g_evict_seq gl' in
    let tl = thread_log gl (p - 1) in
    let et = VT.blum_evict_seq tl in
    if i1 < length es' then (
      if i2 < length es' then 
        lemma_evict_elem_unique_aux gl' i1 i2
      else (
        lemma_evict_elem_tids gl' i1;
        //assert(MH.thread_id_of (index es i1) < (p - 1));
        VT.lemma_evict_elem_tid tl
      )
    )
    else 
      lemma_evict_elem_unique tl (i1 - length es') (i2 - length es')
    
  )


let lemma_evict_elem_unique (gl: verifiable_log) (i1 i2: seq_index (g_evict_seq gl)):
  Lemma (requires (i1 <> i2))
        (ensures (diff_elem  (g_evict_seq gl) i1 i2))
        [SMTPat (diff_elem (g_evict_seq gl) i1 i2)] = 
  if i1 < i2 then
    lemma_evict_elem_unique_aux gl i1 i2
  else 
    lemma_evict_elem_unique_aux gl i2 i1

let lemma_evict_elem_unique2 (gl: verifiable_log):
  Lemma (uniq_prop (g_evict_seq gl)) =   
  ()


let lemma_evict_elem_count (gl: verifiable_log) (x: ms_hashfn_dom):
  Lemma (count x (g_evict_seq gl) <= 1) = 
  lemma_evict_elem_unique2 gl;
  lemma_uniq_prop_counts (g_evict_seq gl) x;
  ()
 
(* the global evict set is a set (not a multiset) *)
let g_evict_set_is_set (gl: verifiable_log): 
  Lemma (is_set (g_evict_set gl)) = 
  let es = g_evict_set gl in
  let aux (x:ms_hashfn_dom):
    Lemma (requires True)
          (ensures (MS.mem x es <= 1))
          [SMTPat (MS.mem x es)] = 
    lemma_evict_elem_count gl x;
    lemma_count_mem (g_evict_seq gl) x
  in
  //assert(is_set es);
  ()

let rec evict_seq_map_aux (gl: verifiable_log) (ii: sseq_index gl {is_evict_to_blum (indexss gl ii)}):
  Tot (j: seq_index (g_evict_seq gl) {index (g_evict_seq gl) j = 
                                      blum_evict_elem gl ii})
  (decreases (length gl)) = 
  let (tid, i) = ii in
  let p = length gl in
  let gl' = prefix gl (p - 1) in
  let s' = g_evict_seq gl' in
  let tl = thread_log gl (p - 1) in
  
  if tid = p - 1 then
    length s' + VT.evict_seq_map tl i
  else
    evict_seq_map_aux gl' ii

let evict_seq_map = evict_seq_map_aux

let rec evict_seq_map_inv_aux (gl: verifiable_log) (j: seq_index (g_evict_seq gl)):
  Tot (ii: sseq_index gl {is_evict_to_blum (indexss gl ii) /\
                          blum_evict_elem gl ii = index (g_evict_seq gl) j /\
                          evict_seq_map gl ii = j})
  (decreases (length gl)) = 
  let p = length gl in
  let gl' = prefix gl (p - 1) in
  let s' = g_evict_seq gl' in
  let tl = thread_log gl (p - 1) in  
  let s = g_evict_seq gl in

  if j < length s' then
    evict_seq_map_inv_aux gl' j
  else
    let j' = j - length s' in
    let i = VT.evict_seq_inv_map tl j' in
    (p-1, i)

let evict_seq_map_inv = evict_seq_map_inv_aux

let rec lemma_evict_seq_inv_aux (gl: verifiable_log) (ii: sseq_index gl {is_evict_to_blum (indexss gl ii)}):
  Lemma (requires True)
        (ensures (evict_seq_map_inv gl (evict_seq_map gl ii) = ii))
        (decreases (length gl)) = 
  let (tid,i) = ii in
  let p = length gl in
  let gl' = prefix gl (p - 1) in
  let s' = g_evict_seq gl' in
  let tl = thread_log gl (p - 1) in

  if tid = p - 1 then ()
  else 
    lemma_evict_seq_inv_aux gl' ii

let lemma_evict_seq_inv = lemma_evict_seq_inv_aux
