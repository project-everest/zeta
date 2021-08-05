module Veritas.Verifier.Global

module MS = Veritas.MultiSet

let lemma_prefix_verifiable (gl: verifiable_log) (i:seq_index gl):
  Lemma (ensures (verifiable (prefix gl i)))
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

let hadd_hevict_equal (epmax: epoch) (gl: hash_verifiable_log epmax) (ep: epoch{ep <= epmax}):
  Lemma (ensures (hadd gl ep = hevict gl ep)) =
  assert(hash_verifiable_prop gl epmax ep);
  ()

(* global add sequence *)
let rec g_add_seq (ep: epoch) (gl: verifiable_log):
  Tot (seq (ms_hashfn_dom))
  (decreases (length gl)) =
  let p = length gl in
  if p = 0 then empty #(ms_hashfn_dom)
  else (
    let gl' = prefix gl (p - 1) in
    lemma_prefix_verifiable gl (p - 1);
    append (g_add_seq ep gl') (blum_add_seq ep (thread_log gl (p - 1)))
  )

(* the hadd that the verifier computes is the multiset hash of all the adds *)
let rec lemma_g_hadd_correct (ep: epoch) (gl: verifiable_log):
  Lemma (ensures (hadd gl ep = ms_hashfn (g_add_seq ep gl)))
        (decreases (length gl)) =
  let p = length gl in
  let s = g_add_seq ep gl in
  let h = hadd gl ep in

  if p = 0 then
    lemma_hashfn_empty()

  else (
    let gl' = prefix gl (p - 1) in
    let s' = g_add_seq ep gl' in
    let h' = hadd gl' ep in

    lemma_g_hadd_correct ep gl';
    assert(h' = ms_hashfn s');

    let tl = thread_log gl (p - 1) in
    let st = blum_add_seq ep tl in
    let ht = VT.hadd tl ep in
    lemma_hadd_correct ep tl;

    lemma_hashfn_agg s' st
  )

let rec add_set_map (gl: verifiable_log) (ii: sseq_index gl {is_blum_add (indexss gl ii)}):
  Tot (let e = indexss gl ii in
       let be = blum_add_elem e in
       let ep = epoch_of be in
       let add_seq = g_add_seq ep gl in
       j: seq_index add_seq {index add_seq j = be})
  (decreases (length gl)) =
  let (tid,i) = ii in
  let e = indexss gl ii in
  let be = blum_add_elem e in
  let ep = epoch_of be in
  let p = length gl in
  let gl' = prefix gl (p - 1) in
  let s' = g_add_seq ep gl' in
  let tl = thread_log gl (p - 1) in

  if tid = p - 1 then
    length s' + (VT.add_seq_map tl i)
  else
    add_set_map gl' ii

(* inverse mapping from add_seq to the blum add entries in the verifier logs *)
let rec add_set_map_inv (ep: epoch) (gl: verifiable_log) (j: seq_index (g_add_seq ep gl)):
  Tot (ii: sseq_index gl {let e = indexss gl ii in
                      is_blum_add e /\
                      (let be = blum_add_elem e in
                       let add_seq = g_add_seq ep gl in
                       be = index add_seq j /\
                       add_set_map gl ii = j /\
                       ep = epoch_of be)})
  (decreases (length gl)) =
  let p = length gl in
  let gl' = prefix gl (p - 1) in
  let s' = g_add_seq ep gl' in
  let tl = thread_log gl (p - 1) in
  let s = g_add_seq ep gl in
  if j < length s' then
    add_set_map_inv ep gl' j
  else
    let j' = j - length s' in
    let i = VT.add_seq_inv_map ep tl j' in
    (p-1, i)

let rec lemma_add_set_map_inv (gl: verifiable_log)(ii: sseq_index gl {is_blum_add (indexss gl ii)}):
  Lemma (ensures (let e = indexss gl ii in
                  let be = blum_add_elem e in
                  let ep = epoch_of be in
                  let j = add_set_map gl ii in
                  add_set_map_inv ep gl j = ii))
        (decreases (length gl)) =
  let (tid,i) = ii in
  let p = length gl in
  let gl' = prefix gl (p - 1) in
  let e = indexss gl ii in
  let be = blum_add_elem e in
  let ep = epoch_of be in
  let s' = g_add_seq ep gl' in
  let tl = thread_log gl (p - 1) in

  if tid = p - 1 then ()
  else
    lemma_add_set_map_inv gl' ii

let rec g_evict_seq (ep: epoch) (gl: verifiable_log):
  Tot (seq (ms_hashfn_dom))
  (decreases (length gl)) =
  let p = length gl in
  if p = 0 then empty #(ms_hashfn_dom)
  else
    let gl' = prefix gl (p - 1) in
    append (g_evict_seq ep gl') (blum_evict_seq ep (thread_log gl (p - 1)))

let rec lemma_ghevict_correct (ep: epoch) (gl: verifiable_log):
  Lemma (ensures (hevict gl ep = ms_hashfn (g_evict_seq ep gl)))
        (decreases (length gl)) =
  let p = length gl in
  let s = g_evict_seq ep gl in
  let h = hevict gl ep in

  if p = 0 then
    lemma_hashfn_empty()
  else (
    let gl' = prefix gl (p - 1) in
    let s' = g_evict_seq ep gl' in
    let h' = hevict gl' ep in

    lemma_ghevict_correct ep gl';

    let tl = thread_log gl (p - 1) in
    let st = blum_evict_seq ep tl in
    let ht = VT.hevict tl ep in
    lemma_hevict_correct ep tl;

    lemma_hashfn_agg s' st
  )

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

let rec lemma_evict_elem_tids (ep: epoch) (gl: verifiable_log) (i: seq_index (g_evict_seq ep gl)):
  Lemma (ensures (MH.thread_id_of (index (g_evict_seq ep gl) i) < length gl))
        (decreases (length gl)) =
  let p = length gl in
  let es = g_evict_seq ep gl in
  if p = 0 then ()
  else
    let gl' = prefix gl (p - 1) in
    let es' = g_evict_seq ep gl' in

    if i < length es' then
      lemma_evict_elem_tids ep gl' i
    else
      VT.lemma_evict_elem_tid ep (thread_log gl (p - 1))

#push-options "--z3rlimit_factor 2"

let rec lemma_evict_elem_unique_aux (ep: epoch) (gl: verifiable_log) (i1 i2: seq_index (g_evict_seq ep gl)):
  Lemma (requires (i1 < i2))
        (ensures (diff_elem  (g_evict_seq ep gl) i1 i2))
        (decreases (length gl)) =
  let p = length gl in
  let es = g_evict_seq ep gl in
  if p = 0 then ()
  else (
    let gl' = prefix gl (p - 1) in
    let es' = g_evict_seq ep gl' in
    let tl = thread_log gl (p - 1) in
    let et = VT.blum_evict_seq ep tl in
    if i1 < length es' then (
      if i2 < length es' then
        lemma_evict_elem_unique_aux ep gl' i1 i2
      else (
        lemma_evict_elem_tids ep gl' i1;
        //assert(MH.thread_id_of (index es i1) < (p - 1));
        VT.lemma_evict_elem_tid ep tl
      )
    )
    else
      lemma_evict_elem_unique ep tl (i1 - length es') (i2 - length es')

  )

#pop-options

let lemma_evict_elem_unique (ep: epoch) (gl: verifiable_log) (i1 i2: seq_index (g_evict_seq ep gl)):
  Lemma (requires (i1 <> i2))
        (ensures (diff_elem  (g_evict_seq ep gl) i1 i2))
        [SMTPat (diff_elem (g_evict_seq ep gl) i1 i2)] =
  if i1 < i2 then
    lemma_evict_elem_unique_aux ep gl i1 i2
  else
    lemma_evict_elem_unique_aux ep gl i2 i1

let lemma_evict_elem_unique2 (ep: epoch) (gl: verifiable_log):
  Lemma (uniq_prop (g_evict_seq ep gl)) =
  ()


let lemma_evict_elem_count (ep: epoch) (gl: verifiable_log) (x: ms_hashfn_dom):
  Lemma (count x (g_evict_seq ep gl) <= 1) =
  lemma_evict_elem_unique2 ep gl;
  lemma_uniq_prop_counts (g_evict_seq ep gl) x;
  ()

(* the global evict set is a set (not a multiset) *)
let g_evict_set_is_set (ep: epoch) (gl: verifiable_log):
  Lemma (is_set (g_evict_set ep gl)) =
  let es = g_evict_set ep gl in
  let aux (x:ms_hashfn_dom):
    Lemma (requires True)
          (ensures (MS.mem x es <= 1))
          [SMTPat (MS.mem x es)] =
    lemma_evict_elem_count ep gl x;
    seq2mset_mem #_ #ms_hashfn_dom_cmp (g_evict_seq ep gl) x
  in
  //assert(is_set es);
  ()

#push-options "--z3rlimit_factor 3"

let rec evict_seq_map (gl: verifiable_log) (ii: sseq_index gl {is_evict_to_blum (indexss gl ii)}):
  Tot (let e = indexss gl ii in
   let be = blum_evict_elem gl ii in
   let ep = epoch_of be in
   let evict_seq = g_evict_seq ep gl in
   j: seq_index evict_seq {index evict_seq j = be})
  (decreases (length gl)) =
  let (tid, i) = ii in
  let be = blum_evict_elem gl ii in
  let ep = epoch_of be in
  let p = length gl in
  let gl' = prefix gl (p - 1) in
  let s' = g_evict_seq ep gl' in
  let tl = thread_log gl (p - 1) in
  if tid = p - 1 then
    length s' + VT.evict_seq_map tl i
  else
    evict_seq_map gl' ii
#pop-options

#push-options "--z3rlimit_factor 3"

let rec evict_seq_map_inv (ep: epoch) (gl: verifiable_log) (j: seq_index (g_evict_seq ep gl)):
  Tot (ii: sseq_index gl {let e = indexss gl ii in
                      is_evict_to_blum e /\
                      (let be = blum_evict_elem gl ii in
                       let evict_seq = g_evict_seq ep gl in
                       be = index evict_seq j /\
                       evict_seq_map gl ii = j /\
                       ep = epoch_of be)})
  (decreases (length gl)) =
  let p = length gl in
  let gl' = prefix gl (p - 1) in
  let s' = g_evict_seq ep gl' in
  let tl = thread_log gl (p - 1) in
  let s = g_evict_seq ep gl in

  if j < length s' then
    evict_seq_map_inv ep gl' j
  else
    let j' = j - length s' in
    let i = VT.evict_seq_inv_map ep tl j' in
    (p-1, i)
#pop-options

let rec lemma_evict_seq_inv (gl: verifiable_log) (ii: sseq_index gl {is_evict_to_blum (indexss gl ii)}):
  Lemma (ensures (let e = indexss gl ii in
                  let be = blum_evict_elem gl ii in
                  let ep = epoch_of be in
                  let j = evict_seq_map gl ii in
                  evict_seq_map_inv ep gl j = ii))
        (decreases (length gl)) =
  let (tid,i) = ii in
  let e = indexss gl ii in
  let be = blum_evict_elem gl ii in
  let ep = epoch_of be in
  let p = length gl in
  let gl' = prefix gl (p - 1) in
  let s' = g_evict_seq ep gl' in
  let tl = thread_log gl (p - 1) in

  if tid = p - 1 then ()
  else
    lemma_evict_seq_inv gl' ii

let rec prefix_upto_epoch (ep: epoch) (gl: verifiable_log):
  Tot (gl':verifiable_log {length gl' = length gl})
  (decreases (length gl)) =

  let p = length gl in
  if p = 0 then empty #(vlog)
  else (
    let gl' = prefix gl (p - 1) in
    let pgl' = prefix_upto_epoch ep gl' in
    let _, lep = VT.prefix_upto_epoch ep (thread_log gl (p - 1)) in
    let pgl = append1 pgl' lep in
    let aux (tid: seq_index pgl):
      Lemma (ensures (VT.verifiable (thread_log pgl tid)))
            [SMTPat (thread_log pgl tid)] =
      if tid = p - 1 then ()
      else
        assert(thread_log pgl tid = thread_log pgl' tid)
    in
    pgl
  )

let rec lemma_prefix_upto_epoch (ep: epoch) (gl: verifiable_log) (tid: seq_index gl):
  Lemma (ensures (let tl = thread_log gl tid in
                  let _, l_ep = VT.prefix_upto_epoch ep tl in
                  let gl_ep = prefix_upto_epoch ep gl in
                  l_ep = index gl_ep tid))
  (decreases (length gl)) =
  let n = length gl in
  assert(n > 0);

  if tid = n - 1 then ()
  else
    lemma_prefix_upto_epoch ep (prefix gl (n - 1)) tid
