module Veritas.Intermediate.Blum

open Veritas.Interleave
open Veritas.SeqAux

module S = FStar.Seq
module SA = Veritas.SeqAux

let rec add_seq_aux #vcfg (ils: its_log vcfg):
  Tot (seq ms_hashfn_dom)
  (decreases (I.length ils)) = 
  let n = I.length ils in
  if n = 0 then S.empty #ms_hashfn_dom
  else
    let ils' = I.prefix ils (n - 1) in
    let s' = add_seq_aux ils' in
    let e = I.index ils (n - 1) in
    if is_blum_add e then 
      append1 s' (IntT.blum_add_elem e)
    else
      s'

let add_seq = add_seq_aux

#push-options "--z3rlimit_factor 3"

/// map an index of ts containing a blum add to its position in the ts_add_seq
///  TODO: No idea why this proof is stressing out F*/Z3
let rec add_seq_map 
  #vcfg
  (itsl: its_log vcfg) 
  (i: I.seq_index itsl{is_blum_add (I.index itsl i)}): 
  Tot (j:SA.seq_index (add_seq itsl){S.index (add_seq itsl) j = 
                                     blum_add_elem itsl i})
  (decreases (I.length itsl)) =      
  let n = I.length itsl in
  let s = add_seq itsl in
  if n = 0 
  then 0    
  else 
    let itsl' = I.prefix itsl (n - 1) in
    let s' = add_seq itsl' in
    if i = n - 1 then S.length s'
    else 
      //add_seq_map itsl' i
      let e = I.index itsl (n - 1) in
      if is_blum_add e then (
        // assert(add_seq itsl == append1 s' (IntT.blum_add_elem e));
        add_seq_map itsl' i
      )
      else 
        add_seq_map itsl' i        

#pop-options

#push-options "--z3rlimit_factor 3"

let rec add_seq_map_inv #vcfg (itsl: its_log vcfg) (j: SA.seq_index (add_seq itsl)):
  Tot (i: I.seq_index itsl {is_blum_add (I.index itsl i) /\ 
                            add_seq_map itsl i = j})
  (decreases (I.length itsl)) = 
  let n = I.length itsl in
  let s = add_seq itsl in
  if n = 0 then 0
  else (
    let itsl' = I.prefix itsl (n - 1) in
    let s' = add_seq itsl' in
    let e = I.index itsl (n - 1) in
    if is_blum_add e then (
      assert(s == SA.append1 s' (IntT.blum_add_elem e));
      if j = S.length s' then n - 1
      else add_seq_map_inv itsl' j        
    )
    else add_seq_map_inv itsl' j 
  )

#pop-options

let rec lemma_add_seq_map_inv #vcfg (itsl: its_log vcfg) (i: I.seq_index itsl{is_blum_add (I.index itsl i)}):
  Lemma (ensures (add_seq_map_inv itsl (add_seq_map itsl i) = i))
        (decreases (I.length itsl))
        [SMTPat (add_seq_map itsl i)] = 
  let n = I.length itsl in
  let s = add_seq itsl in
  if n = 0 then ()
  else 
    let itsl' = I.prefix itsl (n - 1) in
    let s' = add_seq itsl' in
    if i = n - 1 then ()
    else 
      lemma_add_seq_map_inv itsl' i  

let lemma_add_elem_correct (#vcfg:_) (itsl: its_log vcfg) (i: I.seq_index itsl):
  Lemma (requires (is_blum_add (I.index itsl i)))
        (ensures (add_set itsl `contains` blum_add_elem itsl i)) =
  let sa = add_seq itsl in        
  let j = add_seq_map itsl i in
  //assert(S.index sa j = blum_add_elem (I.index itsl i));
  mset_contains_seq_element #_ #ms_hashfn_dom_cmp sa j    

/// into mapping from ts add seq to global add seq
let global_to_ts_addset_map_aux #vcfg (itsl: its_log vcfg) (i: SA.seq_index (IntG.add_seq (g_logS_of itsl))):
  Tot (j: SA.seq_index (add_seq itsl) 
       {
          S.index (IntG.add_seq (g_logS_of itsl)) i = 
          S.index (add_seq itsl) j
       }) =          
  let gl = g_logS_of itsl in
  let gs = IntG.add_seq gl in
  let ii = IntG.add_set_map_inv gl i in
  let ts = add_seq itsl in
  let i' = s2i_map itsl ii in
  let j = add_seq_map itsl i' in
  j

open FStar.Classical

let lemma_global_to_ts_addset_map_into #vcfg (itsl: its_log vcfg):
  Lemma (forall (i1: SA.seq_index (IntG.add_seq (g_logS_of itsl))).
         forall (i2: SA.seq_index (IntG.add_seq (g_logS_of itsl))).
         i1 <> i2 ==> global_to_ts_addset_map_aux itsl i1 <> 
                    global_to_ts_addset_map_aux itsl i2) = 
  let gl = g_logS_of itsl in
  let gs = IntG.add_seq gl in
  
  let aux (i1 i2: SA.seq_index gs):
    Lemma (requires True)
          (ensures (i1 <> i2 ==> global_to_ts_addset_map_aux itsl i1 <>
                               global_to_ts_addset_map_aux itsl i2)) = ()    
  in  
  forall_intro_2 aux

let global_to_ts_addset_map #vcfg (itsl: its_log vcfg):
  into_smap (IntG.add_seq (g_logS_of itsl)) 
       (add_seq itsl) = 
  lemma_global_to_ts_addset_map_into itsl;
  global_to_ts_addset_map_aux itsl

let ts_to_global_addset_map_aux #vcfg (itsl: its_log vcfg) (j: SA.seq_index (add_seq itsl)):
  Tot (i: SA.seq_index (IntG.add_seq (g_logS_of itsl))
       {
          S.index (IntG.add_seq (g_logS_of itsl)) i = 
          S.index (add_seq itsl) j
       }) = 
 let gl = g_logS_of itsl in
 let gs = IntG.add_seq gl in
 let ts = add_seq itsl in
 let i' = add_seq_map_inv itsl j in  
 let ii = i2s_map itsl i' in
 let i = IntG.add_set_map gl ii in
 i

let lemma_ts_to_global_addset_map_into #vcfg (itsl: its_log vcfg):
  Lemma (forall (i1: SA.seq_index (add_seq itsl)).
         forall (i2: SA.seq_index (add_seq itsl)).
           i1 <> i2 ==> ts_to_global_addset_map_aux itsl i1 <>
                      ts_to_global_addset_map_aux itsl i2) = 
  let gl = g_logS_of itsl in
  let gs = IntG.add_seq gl in
  let ts = add_seq itsl in

  let aux (i1 i2: SA.seq_index ts):
    Lemma (i1 <> i2 ==> ts_to_global_addset_map_aux itsl i1 <>
                      ts_to_global_addset_map_aux itsl i2) = ()
  in
  forall_intro_2 aux

let ts_to_global_addset_map #vcfg (itsl: its_log vcfg):
  into_smap (add_seq itsl)
            (IntG.add_seq (g_logS_of itsl)) = 
  lemma_ts_to_global_addset_map_into itsl;
  ts_to_global_addset_map_aux itsl


let lemma_add_set_correct (#vcfg:_) (itsl: its_log vcfg): 
  Lemma (ensures (add_set itsl == IntG.add_set (g_logS_of itsl))) = 
  let gl = g_logS_of itsl in
  let gs = IntG.add_seq gl in
  let ts = add_seq itsl in
  
  bijection_seq_mset #_ #ms_hashfn_dom_cmp gs ts (global_to_ts_addset_map itsl)
                             (ts_to_global_addset_map itsl);
  ()

let lemma_add_set_extend  (#vcfg:_) (itsl: its_log vcfg {I.length itsl > 0}):
  Lemma (requires (is_blum_add (I.telem itsl)))
        (ensures (let i = I.length itsl - 1 in
                  let e = I.index itsl i in
                  let be = blum_add_elem itsl i in
                  let itsl' = I.prefix itsl i in
                  add_set itsl == 
                  add_elem (add_set itsl') be)) = 
  let n = I.length itsl in
  let e = I.telem itsl in
  let itsl' = I.prefix itsl (n - 1) in
  let s' = add_seq itsl' in
  let be = IntT.blum_add_elem e in
  seq2mset_add_elem #_ #ms_hashfn_dom_cmp s' be                  

let blum_evict_elem (#vcfg:_) (itsl: its_log vcfg) (i:I.seq_index itsl{is_evict_to_blum (I.index itsl i)}):
  ms_hashfn_dom = 
  let gl = g_logS_of itsl in
  let ii = i2s_map itsl i in
  let (tid,j) = ii in
  let tl = IntG.thread_log gl tid in
  IntG.blum_evict_elem gl ii

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

let rec evict_seq_aux #vcfg (itsl: its_log vcfg): 
  Tot (seq ms_hashfn_dom)
  (decreases (I.length itsl)) = 
  let n = I.length itsl in
  if n = 0 then S.empty #ms_hashfn_dom
  else
    let itsl' = I.prefix itsl (n - 1) in
    let s' = evict_seq_aux itsl' in
    let e = I.index itsl (n - 1) in
    if is_evict_to_blum e then
      SA.append1 s' (blum_evict_elem itsl (n - 1))
    else
      s'

let evict_seq (#vcfg:_) (itsl: its_log vcfg): seq ms_hashfn_dom =
  evict_seq_aux itsl

#push-options "--z3rlimit_factor 3"

let rec evict_seq_map #vcfg (itsl: its_log vcfg) (i:I.seq_index itsl {is_evict_to_blum (I.index itsl i)}):
  Tot (j:SA.seq_index (evict_seq itsl){S.index (evict_seq itsl) j = 
                                          blum_evict_elem itsl i}) 
  (decreases (I.length itsl)) = 
  let n = I.length itsl in
  let itsl' = I.prefix itsl (n - 1) in
  let s' = evict_seq itsl' in
  if i = n - 1 then S.length s'
  else ( 
    lemma_blum_evict_elem itsl (n - 1) i;
    let e = I.index itsl (n - 1) in
    if is_evict_to_blum e then 
      evict_seq_map itsl' i
    
    else 
      evict_seq_map itsl' i
    
  )
  
#pop-options

let evict_set_correct (#vcfg:_) (itsl: its_log vcfg):
  Lemma (ensures (evict_set itsl == IntG.evict_set (g_logS_of itsl))) = 
  admit()

let lemma_evict_set_extend2 (#vcfg:_) (itsl: its_log vcfg{I.length itsl > 0}):
  Lemma (requires (let i = I.length itsl - 1 in  
                   not (is_evict_to_blum (I.index itsl i))))
        (ensures (let i = I.length itsl - 1 in  
                  evict_set itsl == evict_set (I.prefix itsl i))) = admit()

let lemma_spec_rel_implies_same_add_elem (#vcfg:_) 
                                         (ils: its_log vcfg{spec_rel ils}) 
                                         (i: I.seq_index ils{is_blum_add (I.index ils i)}):
  Lemma (ensures (let ilk = IntTS.to_logk ils in
                  SpecV.is_blum_add (I.index ilk i) /\
                  SpecT.blum_add_elem (I.index ilk i) = blum_add_elem ils i)) = admit()
 
let lemma_spec_rel_implies_same_add_seq (#vcfg:_) (ils: its_log vcfg{spec_rel ils})
  : Lemma (ensures (let ilk = to_logk ils in 
                    add_seq ils = SpecB.ts_add_seq ilk))
  = admit()

let lemma_spec_rel_implies_same_evict_elem (#vcfg:_) 
                                         (ils: its_log vcfg{spec_rel ils}) 
                                         (i: I.seq_index ils{is_evict_to_blum (I.index ils i)}):
  Lemma (ensures (let ilk = IntTS.to_logk ils in
                  SpecV.is_evict_to_blum (I.index ilk i) /\
                  SpecB.blum_evict_elem ilk i = blum_evict_elem ils i))
  = admit()                  

let lemma_spec_rel_implies_same_evict_seq (#vcfg:_) (ils: its_log vcfg{spec_rel ils})
  : Lemma (ensures (let ilk = to_logk ils in 
                    evict_seq ils = SpecB.ts_evict_seq ilk))
  = admit()

(* since evict_set is a pure set (not a multiset) we can identify the unique index 
 * for each element of the set *)
let index_blum_evict (#vcfg:_) (itsl: its_log vcfg) (e: ms_hashfn_dom {evict_set itsl `contains` e}):
  (i:I.seq_index itsl{is_evict_to_blum (I.index itsl i) /\ 
                      blum_evict_elem itsl i = e}) = admit()

(* if the blum add occurs in the blum evict set, its index is earlier *)
let lemma_evict_before_add (#vcfg:_) (itsl: its_log vcfg) (i:I.seq_index itsl{is_blum_add (I.index itsl i)}):
  Lemma (ensures (not (evict_set itsl `contains` blum_add_elem itsl i)) \/
                  index_blum_evict itsl (blum_add_elem itsl i) < i) = admit()

let lemma_add_delta_implies_not_eq (#vcfg:_) (itsl: its_log vcfg) (i:nat{i <= I.length itsl}) (be:ms_hashfn_dom):
    Lemma (requires (let itsli = I.prefix itsl i in
                     MS.mem be (add_set itsli) > MS.mem be (evict_set itsli)))
          (ensures (~ ((add_set itsl) == (evict_set itsl)))) = admit()
