module Veritas.Intermediate.Global
#push-options "--max_fuel 1 --max_ifuel 0"

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

let rec add_seq (#vcfg:_) (ep: epoch) (gl: verifiable_log vcfg):
  Tot (seq (ms_hashfn_dom))
  (decreases (S.length gl)) = 
  let p = S.length gl in
  if p = 0 then S.empty #(ms_hashfn_dom)
  else
    let gl' = SA.prefix gl (p - 1) in
    append (add_seq ep gl') (IntT.blum_add_seq ep (thread_log gl (p - 1)))

let rec lemma_g_hadd_correct #vcfg (ep: epoch) (gl: verifiable_log vcfg):
  Lemma (ensures (hadd gl ep = ms_hashfn (add_seq ep gl)))
        (decreases (S.length gl)) = 
  let p = S.length gl in
  let s = add_seq ep gl in
  let h = hadd gl ep in
  if p = 0 then
    lemma_hashfn_empty()
  else (
    let gl' = SA.prefix gl (p - 1) in
    let s' = add_seq ep gl' in
    let h' = hadd gl' ep in
    lemma_g_hadd_correct ep gl';
    assert(h' = ms_hashfn s');

    let tl = thread_log gl (p - 1) in
    let st = blum_add_seq ep tl in
    let ht = IntT.hadd tl ep in
    IntT.lemma_hadd_correct ep tl;
    lemma_hashfn_agg s' st
  )

(* mapping from blum_add entries in verifier log to the index in add seq *)
let rec add_set_map (#vcfg:_) (gl: verifiable_log vcfg) (ii: sseq_index gl {is_blum_add (indexss gl ii)}):
  Tot (let e = indexss gl ii in
   let be = blum_add_elem e in
   let ep = epoch_of be in
   let as = add_seq ep gl in
   j: SA.seq_index as {S.index as j = be})
  (decreases (S.length gl))
  = 
  let (tid, i) = ii in
  let e = indexss gl ii in
  let be = blum_add_elem e in
  let ep = epoch_of be in
  let p = S.length gl in
  let gl' = SA.prefix gl (p - 1) in
  let s' = add_seq ep gl' in
  let tl = thread_log gl (p - 1) in

  if tid = p - 1 then
    S.length s' + (IntT.add_seq_map tl i)
  else
    add_set_map gl' ii

(* inverse mapping from add_seq to the blum add entries in the verifier logs *)
let rec add_set_map_inv (#vcfg:_) (ep: epoch) (gl: verifiable_log vcfg) (j: SA.seq_index (add_seq ep gl)):
  Tot (ii: sseq_index gl {let e = indexss gl ii in
                      is_blum_add e /\
                      (let be = blum_add_elem e in
                       let as = add_seq ep gl in
                       be = S.index as j /\
                       add_set_map gl ii = j /\
                       ep = epoch_of be)})
  (decreases (S.length gl)) =
  let p = S.length gl in
  let gl' = SA.prefix gl (p - 1) in
  let s' = add_seq ep gl' in
  let tl = thread_log gl (p - 1) in

  if j < S.length s' then
    add_set_map_inv ep gl' j
  else
    let j' = j - S.length s' in
    let i = IntT.add_seq_inv_map ep tl j' in
    (p - 1, i)

let rec lemma_add_set_map_inv (#vcfg:_) (gl: verifiable_log vcfg) (ii: sseq_index gl {is_blum_add (indexss gl ii)}):
  Lemma (ensures (let e = indexss gl ii in
                  let be = blum_add_elem e in
                  let ep = epoch_of be in
                  let j = add_set_map gl ii in
                  add_set_map_inv ep gl j = ii))
        (decreases (S.length gl)) =
  let e = indexss gl ii in
  let be = blum_add_elem e in
  let ep = epoch_of be in
  let (tid, i) = ii in
  let p = S.length gl in
  let gl' = SA.prefix gl (p - 1) in
  let s' = add_seq ep gl' in
  let tl = thread_log gl (p - 1) in

  if tid = p - 1 then ()
  else
    lemma_add_set_map_inv gl' ii

(* a single sequence containing all the blum evicts *)
let rec evict_seq (#vcfg:_) (ep: epoch) (gl: verifiable_log vcfg):
  Tot (seq ms_hashfn_dom)
  (decreases (S.length gl)) =
  let p = S.length gl in
  if p = 0 then S.empty #(ms_hashfn_dom)
  else
    let gl' = SA.prefix gl (p - 1) in
    append (evict_seq ep gl') (IntT.blum_evict_seq ep (thread_log gl (p - 1)))

let rec lemma_ghevict_correct (#vcfg:_) (ep: epoch) (gl: verifiable_log vcfg):
  Lemma (ensures (hevict gl ep = ms_hashfn (evict_seq ep gl)))
        (decreases (S.length gl)) = 
  let p = S.length gl in
  let s = evict_seq ep gl in
  let h = hevict gl ep in
  if p = 0 then
    lemma_hashfn_empty()
  else (
    let gl' = SA.prefix gl (p - 1) in
    let s' = evict_seq ep gl' in
    let h' = hevict gl' ep in
    lemma_ghevict_correct ep gl';
    let tl = thread_log gl (p - 1) in
    let st = IntT.blum_evict_seq ep tl in
    let ht = IntT.hevict tl ep in
    IntT.lemma_hevict_correct ep tl;
    
    lemma_hashfn_agg s' st
  )
        
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

let rec lemma_evict_elem_tids #vcfg (ep: epoch) (gl: verifiable_log vcfg) (i: SA.seq_index (evict_seq ep gl))
  : Lemma (ensures (let es = evict_seq ep gl in
                    MH.thread_id_of (S.index es i) < S.length gl))
          (decreases (S.length gl)) = 
  let p = S.length gl in
  let es = evict_seq ep gl in
  if p = 0 then ()
  else
    let gl' = SA.prefix gl (p - 1) in
    let es' = evict_seq ep gl' in
    if i < S.length es' then
      lemma_evict_elem_tids ep gl' i
    else      
      IntT.lemma_evict_elem_tid ep (thread_log gl (p - 1))

let rec lemma_evict_elem_unique_aux #vcfg (ep: epoch) (gl: verifiable_log vcfg)
  (i1 i2: SA.seq_index (evict_seq ep gl))
  : Lemma (requires (i1 < i2))
          (ensures (diff_elem (evict_seq ep gl) i1 i2))
          (decreases (S.length gl)) = 
  let p = S.length gl in
  let es = evict_seq ep gl in
  if p = 0 then ()
  else
    let gl' = SA.prefix gl (p - 1) in
    let es' = evict_seq ep gl' in
    let tl = thread_log gl (p - 1) in
    let et = IntT.blum_evict_seq ep tl in
    if i1 < S.length es' then
      if i2 < S.length es' then
        lemma_evict_elem_unique_aux ep gl' i1 i2
      else (
        lemma_evict_elem_tids ep gl' i1;
        IntT.lemma_evict_elem_tid ep tl
      )
    else
      IntT.lemma_evict_elem_unique ep tl (i1 - S.length es') (i2 - S.length es')

let lemma_evict_elem_unique #vcfg (ep: epoch) (gl: verifiable_log vcfg) (i1 i2: SA.seq_index (evict_seq ep gl))
  : Lemma (requires (i1 <> i2))
          (ensures (diff_elem (evict_seq ep gl) i1 i2))
          [SMTPat (diff_elem (evict_seq ep gl) i1 i2)] =
  if i1 < i2 then
    lemma_evict_elem_unique_aux ep gl i1 i2
  else
    lemma_evict_elem_unique_aux ep gl i2 i1

let lemma_evict_elem_unique2 #vcfg (ep: epoch) (gl: verifiable_log vcfg):
  Lemma (uniq_prop (evict_seq ep gl)) = ()

let lemma_evict_elem_count #vcfg (ep: epoch) (gl: verifiable_log vcfg) (x: ms_hashfn_dom)
  : Lemma (count x (evict_seq ep gl) <= 1) =
  lemma_evict_elem_unique2 ep gl;
  lemma_uniq_prop_counts (evict_seq ep gl) x


module MS = Veritas.MultiSet

(* the global evict set is a set (not a multiset) *)
let evict_set_is_set (#vcfg:_) (ep: epoch) (gl: verifiable_log vcfg):
  Lemma (ensures (is_set (evict_set ep gl))) =
  let es = evict_set ep gl in
  let aux (x:ms_hashfn_dom):
    Lemma (ensures (MS.mem x es <= 1))
          [SMTPat (MS.mem x es)] = 
      lemma_evict_elem_count ep gl x;
      seq2mset_mem #_ #ms_hashfn_dom_cmp (evict_seq ep gl) x
  in
  ()

let rec evict_seq_map (#vcfg:_) (gl: verifiable_log vcfg) (ii: sseq_index gl {is_evict_to_blum (indexss gl ii)}):
  Tot (let e = indexss gl ii in
   let be = blum_evict_elem gl ii in
   let ep = epoch_of be in
   let es = evict_seq ep gl in
   j: SA.seq_index es {S.index es j = be})
  (decreases (S.length gl)) =
  let (tid, i) = ii in
  let e = indexss gl ii in
  let be = blum_evict_elem gl ii in
  let ep = epoch_of be in

  let p = S.length gl in
  let gl' = SA.prefix gl (p - 1) in
  let s' = evict_seq ep gl' in
  let tl = thread_log gl (p - 1) in

  if tid = p - 1 then
    S.length s' + IntT.evict_seq_map tl i
  else
    evict_seq_map gl' ii

let rec evict_seq_map_inv (#vcfg:_) (ep: epoch) (gl: verifiable_log vcfg) (j: SA.seq_index (evict_seq ep gl)):
  Tot (ii: sseq_index gl {let e = indexss gl ii in
                      is_evict_to_blum e /\
                      (let be = blum_evict_elem gl ii in
                       let es = evict_seq ep gl in
                       be = S.index es j /\
                       ep = epoch_of be /\
                       evict_seq_map gl ii = j)})
  (decreases (S.length gl)) =
  let p = S.length gl in
  let gl' = SA.prefix gl (p - 1) in
  let s' = evict_seq ep gl' in
  let tl = thread_log gl (p - 1) in
  if j < S.length s' then
    evict_seq_map_inv ep gl' j
  else
    let j' = j - S.length s' in
    let i = IntT.evict_seq_inv_map ep tl j' in
    (p-1, i)

#push-options "--z3rlimit_factor 2"

let rec lemma_evict_seq_inv (#vcfg:_) (gl: verifiable_log vcfg)
  (ii: sseq_index gl {is_evict_to_blum (indexss gl ii)}):
  Lemma (ensures (let e = indexss gl ii in
                  let be = blum_evict_elem gl ii in
                  let ep = epoch_of be in
                  let j = evict_seq_map gl ii in
                  evict_seq_map_inv ep gl j = ii))
        (decreases (S.length gl)) =
  let e = indexss gl ii in
  let be = blum_evict_elem gl ii in
  let ep = epoch_of be in

  let (tid, i) = ii in
  let p = S.length gl in
  let gl' = SA.prefix gl (p - 1) in
  let s' = evict_seq ep gl' in
  let tl = thread_log gl (p - 1) in
  if tid = p - 1 then ()
  else
    lemma_evict_seq_inv gl' ii

#pop-options

let hadd_hevict_equal (#vcfg:_) (epmax: epoch) (gl: hash_verifiable_log vcfg epmax) (ep: epoch{ep <= epmax}):
  Lemma (ensures (hadd gl ep = hevict gl ep /\
                  ms_hashfn (add_seq ep gl) = ms_hashfn (evict_seq ep gl))) =
  assert(hash_verifiable_prop gl epmax ep);
  lemma_ghevict_correct ep gl;
  lemma_g_hadd_correct ep gl

let rec prefix_upto_epoch (#vcfg:_) (ep: epoch) (gl: verifiable_log vcfg)
  : Tot (gl': verifiable_log vcfg {S.length gl = S.length gl' })
  (decreases (S.length gl)) =

  let p = S.length gl in
  if p = 0 then S.empty #(logS vcfg)
  else (
    let gl' = SA.prefix gl (p - 1) in
    let pgl' = prefix_upto_epoch ep gl' in
    let _, lep = IntT.prefix_upto_epoch ep (thread_log gl (p - 1)) in
    let pgl = append1 pgl' lep in
    let aux (tid: SA.seq_index pgl):
      Lemma (ensures (IntT.verifiable (thread_log pgl tid)))
            [SMTPat (thread_log pgl tid)] =
      if tid = p - 1 then ()
      else
        assert(thread_log pgl tid = thread_log pgl' tid)
    in
    pgl
  )

let rec lemma_prefix_upto_epoch (#vcfg:_) (ep: epoch) (gl: verifiable_log vcfg) (tid: SA.seq_index gl):
  Lemma (ensures (let tl = thread_log gl tid in
                  let _, l_ep = IntT.prefix_upto_epoch ep tl in
                  let gl_ep = prefix_upto_epoch ep gl in
                  l_ep = S.index gl_ep tid))
  (decreases (S.length gl)) =
  let n = S.length gl in
  assert(n > 0);

  if tid = n - 1 then ()
  else
    lemma_prefix_upto_epoch ep (SA.prefix gl (n - 1)) tid
