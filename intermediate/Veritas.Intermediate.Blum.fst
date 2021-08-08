module Veritas.Intermediate.Blum

open Veritas.Interleave
open Veritas.SeqAux

module S = FStar.Seq
module SA = Veritas.SeqAux

let rec add_seq #vcfg (ep: epoch) (ils: its_log vcfg):
  Tot (seq ms_hashfn_dom)
  (decreases (I.length ils)) =
  let n = I.length ils in
  if n = 0 then S.empty #ms_hashfn_dom
  else
    let ils' = I.prefix ils (n - 1) in
    let s' = add_seq ep ils' in
    let e = I.index ils (n - 1) in
    if is_blum_add e && ep = epoch_of (blum_add_elem e) then
      append1 s' (IntT.blum_add_elem e)
    else
      s'

#push-options "--z3rlimit_factor 3"

/// map an index of ts containing a blum add to its position in the ts_add_seq
///  TODO: No idea why this proof is stressing out F*/Z3
let rec add_seq_map
  #vcfg
  (itsl: its_log vcfg)
  (i: I.seq_index itsl{is_blum_add (I.index itsl i)}):
  Tot (let e = I.index itsl i in
       let be = blum_add_elem e in
       let ep = epoch_of be in
       j:SA.seq_index (add_seq ep itsl){ S.index (add_seq ep itsl) j = be })
  (decreases (I.length itsl)) =
  let n = I.length itsl in
  let e = I.index itsl i in
  let be = blum_add_elem e in
  let ep = epoch_of be in

  let itsl' = I.prefix itsl (n - 1) in
  let s' = add_seq ep itsl' in
  if i = n - 1 then S.length s'
  else
    add_seq_map itsl' i

#pop-options

#push-options "--z3rlimit_factor 3"

let rec add_seq_map_inv #vcfg (ep: epoch) (itsl: its_log vcfg) (j: SA.seq_index (add_seq ep itsl)):
  Tot (i: I.seq_index itsl {let e = I.index itsl i in
                            is_blum_add e /\
                            (let be = blum_add_elem (I.index itsl i) in
                             let add_seq = add_seq ep itsl in
                             be = S.index add_seq j /\
                             add_seq_map itsl i = j /\
                             ep = epoch_of be)})
  (decreases (I.length itsl)) =
  let n = I.length itsl in
  let s = add_seq ep itsl in
  if n = 0 then 0
  else (
    let itsl' = I.prefix itsl (n - 1) in
    let s' = add_seq ep itsl' in
    let e = I.index itsl (n - 1) in
    if is_blum_add e && ep = epoch_of (blum_add_elem (I.index itsl (n-1))) then
      if j = S.length s' then n - 1
      else add_seq_map_inv ep itsl' j
    else add_seq_map_inv ep itsl' j
  )

#pop-options

#push-options "--z3rlimit_factor 4"

let rec lemma_add_seq_map_inv #vcfg (itsl: its_log vcfg) (i: I.seq_index itsl{is_blum_add (I.index itsl i)}):
  Lemma (ensures (let e = I.index itsl i in
                  let be = blum_add_elem e in
                  let ep = epoch_of be in
                  let j = add_seq_map itsl i in
                  add_seq_map_inv ep itsl j = i))
        (decreases (I.length itsl))
        [SMTPat (add_seq_map itsl i)] =

  let n = I.length itsl in
  let itsl' = I.prefix itsl (n - 1) in
  if i = n - 1 then ()
  else
    lemma_add_seq_map_inv itsl' i

#pop-options

let lemma_add_elem_correct (#vcfg:_) (itsl: its_log vcfg) (i: I.seq_index itsl):
  Lemma (requires (is_blum_add (I.index itsl i)))
        (ensures (let e = I.index itsl i in
                  let be = blum_add_elem e in
                  let ep = epoch_of be in
                  add_set ep itsl `contains` be)) =
  let e = I.index itsl i in
  let be = blum_add_elem e in
  let ep = epoch_of be in
  let add_seq = add_seq ep itsl in
  let j = add_seq_map itsl i in
  //assert(S.index sa j = blum_add_elem (I.index itsl i));
  mset_contains_seq_element #_ #ms_hashfn_dom_cmp add_seq j

/// into mapping from ts add seq to global add seq
let global_to_ts_addset_map_aux #vcfg (ep: epoch) (itsl: its_log vcfg)
  (i: SA.seq_index (IntG.add_seq ep (g_logS_of itsl))):
  Tot (j: SA.seq_index (add_seq ep itsl)
       {
          S.index (IntG.add_seq ep (g_logS_of itsl)) i =
          S.index (add_seq ep itsl) j
       }) =
  let gl = g_logS_of itsl in
  let gs = IntG.add_seq ep gl in
  let ii = IntG.add_set_map_inv ep gl i in
  let ts = add_seq ep itsl in
  let i' = s2i_map itsl ii in
  let j = add_seq_map itsl i' in
  j

open FStar.Classical

let lemma_global_to_ts_addset_map_into #vcfg (ep: epoch) (itsl: its_log vcfg):
  Lemma (forall (i1: SA.seq_index (IntG.add_seq ep (g_logS_of itsl))).
         forall (i2: SA.seq_index (IntG.add_seq ep (g_logS_of itsl))).
         i1 <> i2 ==> global_to_ts_addset_map_aux ep itsl i1 <>
                    global_to_ts_addset_map_aux ep itsl i2) =
  let gl = g_logS_of itsl in
  let gs = IntG.add_seq ep gl in

  let aux (i1 i2: SA.seq_index gs):
    Lemma (ensures (i1 <> i2 ==> global_to_ts_addset_map_aux ep itsl i1 <>
                               global_to_ts_addset_map_aux ep itsl i2)) = ()
  in
  forall_intro_2 aux

let global_to_ts_addset_map #vcfg (ep: epoch) (itsl: its_log vcfg):
  into_smap (IntG.add_seq ep (g_logS_of itsl))
       (add_seq ep itsl) =
  lemma_global_to_ts_addset_map_into ep itsl;
  global_to_ts_addset_map_aux ep itsl

let ts_to_global_addset_map_aux #vcfg (ep: epoch) (itsl: its_log vcfg) (j: SA.seq_index (add_seq ep itsl)):
  Tot (i: SA.seq_index (IntG.add_seq ep (g_logS_of itsl))
       {
          S.index (IntG.add_seq ep (g_logS_of itsl)) i =
          S.index (add_seq ep itsl) j
       }) =
 let gl = g_logS_of itsl in
 let gs = IntG.add_seq ep gl in
 let ts = add_seq ep itsl in
 let i' = add_seq_map_inv ep itsl j in
 let ii = i2s_map itsl i' in
 let i = IntG.add_set_map gl ii in
 i

let lemma_ts_to_global_addset_map_into #vcfg (ep: epoch) (itsl: its_log vcfg):
  Lemma (forall (i1: SA.seq_index (add_seq ep itsl)).
         forall (i2: SA.seq_index (add_seq ep itsl)).
           i1 <> i2 ==> ts_to_global_addset_map_aux ep itsl i1 <>
                      ts_to_global_addset_map_aux ep itsl i2) =
  let gl = g_logS_of itsl in
  let gs = IntG.add_seq ep gl in
  let ts = add_seq ep itsl in

  let aux (i1 i2: SA.seq_index ts):
    Lemma (i1 <> i2 ==> ts_to_global_addset_map_aux ep itsl i1 <>
                      ts_to_global_addset_map_aux ep itsl i2) = ()
  in
  forall_intro_2 aux

let ts_to_global_addset_map #vcfg (ep: epoch) (itsl: its_log vcfg):
  into_smap (add_seq ep itsl)
            (IntG.add_seq ep (g_logS_of itsl)) =
  lemma_ts_to_global_addset_map_into ep itsl;
  ts_to_global_addset_map_aux ep itsl


let lemma_add_set_correct (#vcfg:_) (ep: epoch) (itsl: its_log vcfg):
  Lemma (ensures (add_set ep itsl == IntG.add_set ep (g_logS_of itsl))) =
  let gl = g_logS_of itsl in
  let gs = IntG.add_seq ep gl in
  let ts = add_seq ep itsl in

  bijection_seq_mset #_ #ms_hashfn_dom_cmp gs ts (global_to_ts_addset_map ep itsl)
                             (ts_to_global_addset_map ep itsl);
  ()

let lemma_add_set_extend  (#vcfg:_) (itsl: its_log vcfg {I.length itsl > 0}):
  Lemma (requires (is_blum_add (I.telem itsl)))
        (ensures (let i = I.length itsl - 1 in
                  let e = I.index itsl i in
                  let be = blum_add_elem e in
                  let ep = epoch_of be in
                  let itsl' = I.prefix itsl i in
                  add_set ep itsl ==
                  add_elem (add_set ep itsl') be)) =
  let n = I.length itsl in
  let e = I.telem itsl in
  let be = blum_add_elem e in
  let ep = epoch_of be in
  let itsl' = I.prefix itsl (n - 1) in
  let s' = add_seq ep itsl' in
  let be = IntT.blum_add_elem e in
  seq2mset_add_elem #_ #ms_hashfn_dom_cmp s' be

let lemma_blum_evict_elem (#vcfg:_) (itsl: its_log vcfg) (i:nat{i <= I.length itsl}) (j:nat{j < i})
  : Lemma (requires (is_evict_to_blum (I.index itsl j)))
          (ensures (blum_evict_elem itsl j = blum_evict_elem (I.prefix itsl i) j)) =
  let gl = g_logS_of itsl in
  let (t,j') = i2s_map itsl j in
  let tl = thread_log gl t in
  assert(blum_evict_elem itsl j = IntT.blum_evict_elem tl j');

  let itsl' = I.prefix itsl i in
  let gl' = g_logS_of itsl' in
  let tl' = thread_log gl' t in
  lemma_i2s_map_prefix itsl i j;
  //assert(i2s_map itsl j = i2s_map itsl' j);
  //assert(blum_evict_elem itsl' j = VT.blum_evict_elem tl' j');
  lemma_prefix_interleaving itsl i t;
  //assert(tl' = VT.prefix tl (VT.length tl'));
  lemma_blum_evict_elem_prefix tl (IntT.length tl') j'

let rec evict_seq #vcfg (ep: epoch) (itsl: its_log vcfg):
  Tot (seq ms_hashfn_dom)
  (decreases (I.length itsl)) =
  let n = I.length itsl in
  if n = 0 then S.empty #ms_hashfn_dom
  else
    let itsl' = I.prefix itsl (n - 1) in
    let s' = evict_seq ep itsl' in
    let e = I.index itsl (n - 1) in
    if is_evict_to_blum e && epoch_of (blum_evict_elem itsl (n-1)) = ep then
      SA.append1 s' (blum_evict_elem itsl (n - 1))
    else
      s'

#push-options "--z3rlimit_factor 3"

let rec evict_seq_map #vcfg (itsl: its_log vcfg) (i:I.seq_index itsl {is_evict_to_blum (I.index itsl i)}):
  Tot (let be = blum_evict_elem itsl i in
       let ep = epoch_of be in
       j:SA.seq_index (evict_seq ep itsl){S.index (evict_seq ep itsl) j = be})
  (decreases (I.length itsl)) =
  let n = I.length itsl in
  let be = blum_evict_elem itsl i in
  let ep = epoch_of be in
  let itsl' = I.prefix itsl (n - 1) in
  let s' = evict_seq ep itsl' in
  if i = n - 1 then S.length s'
  else (
    lemma_blum_evict_elem itsl (n - 1) i;
    evict_seq_map itsl' i
  )

#pop-options

let rec evict_seq_inv_map #vcfg (ep: epoch) (itsl: its_log vcfg) (j:SA.seq_index (evict_seq ep itsl)):
  Tot (i:I.seq_index itsl {is_evict_to_blum (I.index itsl i) /\
                           (let be = blum_evict_elem itsl i in
                            let evict_seq = evict_seq ep itsl in
                            ep = epoch_of be /\
                            be = S.index evict_seq j /\
                            evict_seq_map itsl i = j)})
  (decreases (I.length itsl)) =
  let n = I.length itsl in
  let itsl' = I.prefix itsl (n - 1) in
  let s' = evict_seq ep itsl' in
  if j = S.length s' then n - 1
  else (
    let i = evict_seq_inv_map ep itsl' j in
    lemma_blum_evict_elem itsl (n-1) i;
    i
  )

#push-options "--z3rlimit_factor 6"

let rec lemma_evict_seq_inv_map #vcfg (itsl: its_log vcfg) (i:I.seq_index itsl {is_evict_to_blum (I.index itsl i)}):
  Lemma (ensures (let be = blum_evict_elem itsl i in
                  let ep = epoch_of be in
                  let j = evict_seq_map itsl i in
                  evict_seq_inv_map ep itsl j = i))
        (decreases (I.length itsl))
        [SMTPat (evict_seq_map itsl i)] =
  let n = I.length itsl in
  let itsl' = I.prefix itsl (n - 1) in
  //let s' = evict_seq itsl' in
  if i = n - 1 then ()
  else (
    lemma_blum_evict_elem itsl (n-1) i;
    lemma_evict_seq_inv_map itsl' i
  )
#pop-options

let global_to_ts_evictseq_map_aux #vcfg (ep: epoch) (itsl: its_log vcfg)
  (i: SA.seq_index (IntG.evict_seq ep (g_logS_of itsl))):
  Tot (j: SA.seq_index (evict_seq ep itsl)
       {
         S.index (IntG.evict_seq ep (g_logS_of itsl)) i =
         S.index (evict_seq ep itsl) j
       }) =
  let gl = g_logS_of itsl in
  let gs = IntG.evict_seq ep gl in
  let ii = IntG.evict_seq_map_inv ep gl i in
  let ts = add_seq ep itsl in
  let i' = s2i_map itsl ii in
  let j = evict_seq_map itsl i' in
  j

let lemma_global_to_ts_evictseq_map_into #vcfg (ep: epoch) (itsl: its_log vcfg):
  Lemma (forall (i1: SA.seq_index (IntG.evict_seq ep (g_logS_of itsl))).
         forall (i2: SA.seq_index (IntG.evict_seq ep (g_logS_of itsl))).
         i1 <> i2 ==> global_to_ts_evictseq_map_aux ep itsl i1 <>
                    global_to_ts_evictseq_map_aux ep itsl i2) =
  let gl = g_logS_of itsl in
  let gs = IntG.evict_seq ep gl in
  let aux (i1 i2: SA.seq_index gs):
    Lemma (requires True)
          (ensures (i1 <> i2 ==> global_to_ts_evictseq_map_aux ep itsl i1 <>
                               global_to_ts_evictseq_map_aux ep itsl i2)) = ()
  in
  forall_intro_2 aux

let global_to_ts_evictseq_map #vcfg (ep: epoch) (itsl: its_log vcfg):
  into_smap (IntG.evict_seq ep (g_logS_of itsl))
            (evict_seq ep itsl) =
  lemma_global_to_ts_evictseq_map_into ep itsl;
  global_to_ts_evictseq_map_aux ep itsl

let ts_to_global_evictseq_map_aux #vcfg (ep: epoch) (itsl: its_log vcfg) (j:SA.seq_index (evict_seq ep itsl)):
  Tot (i: SA.seq_index (IntG.evict_seq ep (g_logS_of itsl))
       {
         S.index (IntG.evict_seq ep (g_logS_of itsl)) i =
         S.index (evict_seq ep itsl) j
       }) =
  let gl = g_logS_of itsl in
  let gs = IntG.evict_seq ep gl in
  let ts = evict_seq ep itsl in
  let i' = evict_seq_inv_map ep itsl j in
  let ii = i2s_map itsl i' in
  let i = IntG.evict_seq_map gl ii in
  i

let lemma_ts_to_global_evictseq_map_into #vcfg (ep: epoch) (itsl: its_log vcfg):
  Lemma (forall (i1: SA.seq_index (evict_seq ep itsl)).
         forall (i2: SA.seq_index (evict_seq ep itsl)).
         i1 <> i2 ==> ts_to_global_evictseq_map_aux ep itsl i1 <>
                    ts_to_global_evictseq_map_aux ep itsl i2) =
  let ts = evict_seq ep itsl in
  let gl = g_logS_of itsl in
  let gs = IntG.evict_seq ep gl in
  let ts = evict_seq ep itsl in
  let aux (j1 j2: SA.seq_index ts):
    Lemma (j1 <> j2 ==> ts_to_global_evictseq_map_aux ep itsl j1 <>
                      ts_to_global_evictseq_map_aux ep itsl j2) = ()
  in
  forall_intro_2 aux

let ts_to_global_evictseq_map #vcfg (ep: epoch) (itsl: its_log vcfg):
  into_smap (evict_seq ep itsl)
            (IntG.evict_seq ep (g_logS_of itsl)) =
  lemma_ts_to_global_evictseq_map_into ep itsl;
  ts_to_global_evictseq_map_aux ep itsl

let evict_set_correct (#vcfg:_) (ep: epoch) (itsl: its_log vcfg):
  Lemma (ensures (evict_set ep itsl == IntG.evict_set ep (g_logS_of itsl))) =
  let gl = g_logS_of itsl in
  let gs = IntG.evict_seq ep gl in
  let ts = evict_seq ep itsl in

  bijection_seq_mset #_ #ms_hashfn_dom_cmp gs ts (global_to_ts_evictseq_map ep itsl)
                             (ts_to_global_evictseq_map ep itsl)

let lemma_evict_elem_correct (#vcfg:_) (itsl: its_log vcfg) (i: I.seq_index itsl):
  Lemma (requires (is_evict_to_blum (I.index itsl i)))
        (ensures (let be = blum_evict_elem itsl i in
                  let ep = epoch_of be in
                  evict_set ep itsl `MS.contains` be)) =
  let be = blum_evict_elem itsl i in
  let ep = epoch_of be in
  let es = evict_seq ep itsl in
  let j = evict_seq_map itsl i in
  mset_contains_seq_element #_ #ms_hashfn_dom_cmp es j

let lemma_evict_set_extend2 (#vcfg:_) (ep: epoch) (itsl: its_log vcfg{I.length itsl > 0}):
  Lemma (requires (let i = I.length itsl - 1 in
                   is_evict_to_blum (I.index itsl i) ==>
                   epoch_of (blum_evict_elem itsl i) <> ep))
        (ensures (let i = I.length itsl - 1 in
                  evict_set ep itsl == evict_set ep (I.prefix itsl i))) = ()

let lemma_spec_rel_implies_same_add_elem (#vcfg:_)
                                         (ils: its_log vcfg{spec_rel ils})
                                         (i: I.seq_index ils{is_blum_add (I.index ils i)}):
  Lemma (ensures (let ilk = IntTS.to_logk ils in
                  SpecV.is_blum_add (I.index ilk i) /\
                  SpecT.blum_add_elem (I.index ilk i) = blum_add_elem (I.index ils i))) =
  ()

let rec lemma_spec_rel_implies_same_add_seq_len #vcfg (ep: epoch) (ils: its_log vcfg{spec_rel ils})
  : Lemma (ensures (let ilk = to_logk ils in
                    S.length (add_seq ep ils) = S.length (SpecB.ts_add_seq ep ilk)))
          (decreases (I.length ils)) =
  let ilk = to_logk ils in
  let as_s = add_seq ep ils in
  let as_k = SpecB.ts_add_seq ep ilk in
  let n = I.length ils in
  if n = 0 then
    SpecB.lemma_add_seq_empty ep ilk
  else (
    let ils' = I.prefix ils (n - 1) in
    let ilk' = to_logk ils' in
    assert(ilk' == I.prefix ilk (n - 1));
    let es = I.index ils (n - 1) in
    let ek = I.index ilk (n - 1) in
    assert(ek = IntTS.to_logK_entry ils (n - 1));
    lemma_spec_rel_implies_prefix_spec_rel ils (n - 1);
    assert(spec_rel ils');
    lemma_spec_rel_implies_same_add_seq_len ep ils';

    if is_blum_add es && epoch_of (blum_add_elem (I.index ils (n-1))) = ep then
      SpecB.lemma_add_seq_extend ilk
    else
      SpecB.lemma_add_seq_extend2 ep ilk
  )

let rec lemma_spec_rel_implies_same_add_seq(#vcfg:_) (ep: epoch) (ils: its_log vcfg{spec_rel ils})
  : Lemma (ensures (let ilk = to_logk ils in
                    add_seq ep ils = SpecB.ts_add_seq ep ilk))
          (decreases (I.length ils)) =
  let ilk = to_logk ils in
  let asl = add_seq ep ils in
  let ask = SpecB.ts_add_seq ep ilk in
  let n = I.length ils in
  if n = 0 then (
    SpecB.lemma_add_seq_empty ep ilk;
    S.lemma_empty ask;
    S.lemma_empty asl
  )
  else (
    let ils' = I.prefix ils (n - 1) in
    let ilk' = to_logk ils' in
    assert(ilk' == I.prefix ilk (n - 1));
    let es = I.index ils (n - 1) in
    let ek = I.index ilk (n - 1) in
    assert(ek = IntTS.to_logK_entry ils (n - 1));
    lemma_spec_rel_implies_prefix_spec_rel ils (n - 1);
    // assert(spec_rel ils');
    lemma_spec_rel_implies_same_add_seq ep ils';
    if is_blum_add es && epoch_of (blum_add_elem (I.index ils (n-1))) = ep then
      // assert(SpecV.is_blum_add ek);
      SpecB.lemma_add_seq_extend ilk
    else
      SpecB.lemma_add_seq_extend2 ep ilk
  )

module SpecTS = Veritas.Verifier.TSLog

let lemma_spec_rel_implies_same_evict_elem (#vcfg:_)
                                         (ils: its_log vcfg{spec_rel ils})
                                         (i: I.seq_index ils{is_evict_to_blum (I.index ils i)}):
  Lemma (ensures (let ilk = IntTS.to_logk ils in
                  SpecV.is_evict_to_blum (I.index ilk i) /\
                  SpecB.blum_evict_elem ilk i = blum_evict_elem ils i)) =
  let ilk = IntTS.to_logk ils in
  // let bes = blum_evict_elem ils i in
  // let bek = SpecB.blum_evict_elem ilk i in
  // let tid = IntTS.thread_id_of ils i in

  // let es = I.index ils i in
  // let ek = I.index ilk i in
  let vss = IntTS.thread_state_pre ils i in
  //let sts = IntV.thread_store vss in
  let vsk = SpecTS.thread_state_pre ilk i in
  //let stk = SpecV.thread_store vsk in
  // assert(ek = IntV.to_logK_entry vss es);
  lemma_blum_evict_def ils i;
  SpecTS.lemma_blum_evict_def ilk i;

  // let s = slot_of es in
  // assert(inuse_slot sts s);
  // let k = stored_key sts s in
  // assert(SpecV.key_of ek = k);

  // let v = stored_value sts s in
  // assert(tid = SpecTS.thread_id_of ilk i);
  lemma_spec_rel_implies_prefix_spec_rel ils i;
  assert(vtls_rel vss vsk);
  // assert(SpecV.store_contains stk k);
  // assert(SpecV.stored_value stk k = v);
  ()

let rec lemma_spec_rel_implies_same_evict_seq (#vcfg:_) (ep: epoch) (ils: its_log vcfg{spec_rel ils})
  : Lemma (ensures (let ilk = to_logk ils in
                    evict_seq ep ils = SpecB.ts_evict_seq ep ilk))
          (decreases (I.length ils))
  =
  let ilk = to_logk ils in
  let esl = evict_seq ep ils in
  let esk = SpecB.ts_evict_seq ep ilk in
  let n = I.length ils in
  if n = 0 then (
    SpecB.lemma_evict_seq_empty ep ilk;
    S.lemma_empty esl;
    S.lemma_empty esk
  )
  else (
    let ils' = I.prefix ils (n - 1) in
    let ilk' = to_logk ils' in
    let es = I.index ils (n - 1) in
    let ek = I.index ilk (n - 1) in
    lemma_spec_rel_implies_prefix_spec_rel ils (n -1);
    lemma_spec_rel_implies_same_evict_seq ep ils';

    if is_evict_to_blum es then (
      lemma_spec_rel_implies_same_evict_elem ils (n - 1);

      if epoch_of (blum_evict_elem ils (n-1)) = ep then
        SpecB.lemma_evict_seq_extend ilk
      else
        SpecB.lemma_evict_seq_extend2 ep ilk
    )
    else
      SpecB.lemma_evict_seq_extend2 ep ilk
  )

(* since evict_set is a pure set (not a multiset) we can identify the unique index
 * for each element of the set *)
let index_blum_evict (#vcfg:_)
  (ep: epoch)
  (itsl: its_log vcfg)
  (e: ms_hashfn_dom {evict_set ep itsl `MS.contains` e}):
  (i:I.seq_index itsl{is_evict_to_blum (I.index itsl i) /\
                      blum_evict_elem itsl i = e}) =
  let esq = evict_seq ep itsl in
  let est = evict_set ep itsl in
  let j = index_of_mselem #_ #ms_hashfn_dom_cmp esq e in
  assert(S.index esq j = e);
  evict_seq_inv_map ep itsl j

(* the clock of an evict entry is the timestamp in the corresponding blum element *)
let lemma_evict_clock  #vcfg (itsl: its_log vcfg) (i:I.seq_index itsl{is_evict_to_blum (I.index itsl i)}):
  Lemma (IntTS.clock itsl i = timestamp_of (blum_evict_elem itsl i)) =
  let gl = g_logS_of itsl in
  let (tid,j) = i2s_map itsl i in
  let tl = thread_log gl tid in
  IntT.lemma_evict_clock tl j

let lemma_add_clock #vcfg (itsl: its_log vcfg) (i: I.seq_index itsl{is_blum_add (I.index itsl i)}):
  Lemma (timestamp_of (blum_add_elem (I.index itsl i)) `ts_lt` IntTS.clock itsl i) =
  let gl = g_logS_of itsl in
  let (tid,j) = i2s_map itsl i in
  let tl = thread_log gl tid in
  IntT.lemma_add_clock tl j

(* if the blum add occurs in the blum evict set, its index is earlier *)
let lemma_evict_before_add (#vcfg:_) (itsl: its_log vcfg) (i:I.seq_index itsl{is_blum_add (I.index itsl i)}):
  Lemma (ensures (let be = blum_add_elem (I.index itsl i) in
                  let ep = epoch_of be in
                  evict_set ep itsl `MS.contains` blum_add_elem (I.index itsl i) ==>
                  index_blum_evict ep itsl be < i)) =
  let be = blum_add_elem (I.index itsl i) in
  let ep = epoch_of be in
  let evt_set = evict_set ep itsl in
  let add_set = add_set ep itsl in
  lemma_add_clock itsl i;
  if evt_set `contains` be then (
    let j = index_blum_evict ep itsl be in
    lemma_evict_clock itsl j;
    lemma_clock_ordering itsl j i
  )
  else ()

/// index of some add element given that the the add set contains the element
///
let some_add_elem_idx (#vcfg:_)
    (ep: epoch)
    (itsl: its_log vcfg)
    (be: ms_hashfn_dom {add_set ep itsl `contains` be}):
   (i:(I.seq_index itsl){is_blum_add (I.index itsl i) /\ be = blum_add_elem (I.index itsl i)}) =
  let s = add_seq ep itsl in
  (* index of element be in s *)
  let j = index_of_mselem #_ #ms_hashfn_dom_cmp s be in
  add_seq_map_inv ep itsl j

let rec lemma_prefix_add_seq #vcfg (ep: epoch) (itsl: its_log vcfg) (i: nat{ i <= I.length itsl}):
  Lemma (ensures (SA.is_prefix (add_seq ep itsl) (add_seq ep (I.prefix itsl i))))
        (decreases (I.length itsl)) =
  let n = I.length itsl in
  if i = n then () // prefix is the same sequence
  else (
    let itsl' = I.prefix itsl (n - 1) in
    let s' = add_seq ep itsl' in
    let e = I.index itsl (n - 1) in
    if i = n - 1 then
      if is_blum_add e && epoch_of (blum_add_elem (I.index itsl (n-1))) = ep then
        lemma_prefix1_append s' (IntT.blum_add_elem e)
      else ()
    else (
      lemma_prefix_add_seq ep itsl' i;
      if is_blum_add e && epoch_of (blum_add_elem (I.index itsl (n-1))) = ep then
        lemma_prefix1_append s' (IntT.blum_add_elem e)
      else ()
    )
  )

let lemma_mem_monotonic_add_set (#vcfg:_) (be:ms_hashfn_dom) (itsl: its_log vcfg) (i:nat{i <= I.length itsl}):
  Lemma (let ep = epoch_of be in
         mem be (add_set ep itsl) >= mem be (add_set ep (I.prefix itsl i))) =
  let itsl' = I.prefix itsl i in
  let ep = epoch_of be in
  let s' = add_seq ep itsl' in
  let s = add_seq ep itsl in
  lemma_prefix_add_seq ep itsl i;
  seq_prefix_mset_mem #_ #ms_hashfn_dom_cmp s s' be;
  ()

#push-options "--z3rlimit_factor 3"

let lemma_add_delta_implies_not_eq (#vcfg:_) (itsl: its_log vcfg) (i:nat{i <= I.length itsl}) (be:ms_hashfn_dom):
    Lemma (requires (let itsli = I.prefix itsl i in
                     let ep = epoch_of be in
                     MS.mem be (add_set ep itsli) > MS.mem be (evict_set ep itsli)))
          (ensures (let ep = epoch_of be in
                    ~ ((add_set ep itsl) == (evict_set ep itsl)))) =
  let ep = epoch_of be in
  let gl = g_logS_of itsl in
  let itsli = I.prefix itsl i in
  let asi = add_set ep itsli in
  let esi = evict_set ep itsli in
  let as = add_set ep itsl in
  let es = evict_set ep itsl in

  let j = some_add_elem_idx ep itsli be in
  lemma_mem_monotonic_add_set be itsl i;

  if es `contains` be then (
    lemma_evict_before_add itsl j;
    let j' = index_blum_evict ep itsl be in
    // assert(j' < j);
    // assert(be = blum_evict_elem itsl j');
    lemma_blum_evict_elem itsl i j';
    // assert(be = blum_evict_elem itsli j');
    lemma_evict_elem_correct itsli j';
    // assert(esi `contains` be);
    // assert(mem be asi > 1);
    // assert(mem be as > 1);
    evict_set_correct ep itsl;
    evict_set_is_set ep gl
  )
  else ()

#pop-options
