module Veritas.Verifier.Blum

open Veritas.EAC
open FStar.Classical

module S = FStar.Seq
module SA = Veritas.SeqAux
module E = Veritas.EAC
module VT = Veritas.Verifier.Thread

let rec ts_add_seq_aux (itsl: its_log): 
  Tot (seq ms_hashfn_dom) 
  (decreases (I.length itsl)) = 
  let n = I.length itsl in
  if n = 0 then S.empty #ms_hashfn_dom
  else
    let itsl' = I.prefix itsl (n - 1) in
    let s' = ts_add_seq_aux itsl' in
    let e = I.index itsl (n - 1) in
    if is_blum_add e then 
      SA.append1 s' (blum_add_elem e)
    else
      s'
  
let ts_add_seq = ts_add_seq_aux

(* map an index of ts containing a blum add to its position in 
 * the ts_add_seq *)
let rec add_seq_map 
  (itsl: its_log) 
  (i: I.seq_index itsl{is_blum_add (I.index itsl i)}): 
  Tot (j:SA.seq_index (ts_add_seq itsl){S.index (ts_add_seq itsl) j = 
                                        blum_add_elem (I.index itsl i)})
  (decreases (I.length itsl)) =                                         
  let n = I.length itsl in
  let s = ts_add_seq itsl in
  if n = 0 then 0    
  else 
    let itsl' = I.prefix itsl (n - 1) in
    let s' = ts_add_seq itsl' in
    if i = n - 1 then S.length s'
    else add_seq_map itsl' i

let rec add_seq_map_inv (itsl: its_log) (j: SA.seq_index (ts_add_seq itsl)):
  Tot (i: I.seq_index itsl {is_blum_add (I.index itsl i) /\ 
                            add_seq_map itsl i = j})
  (decreases (I.length itsl)) = 
  let n = I.length itsl in
  let s = ts_add_seq itsl in
  if n = 0 then 0
  else (
    let itsl' = I.prefix itsl (n - 1) in
    let s' = ts_add_seq itsl' in
    let e = I.index itsl (n - 1) in
    if is_blum_add e then (
      assert(s == SA.append1 s' (blum_add_elem e));
      if j = S.length s' then n - 1
      else add_seq_map_inv itsl' j        
    )
    else add_seq_map_inv itsl' j 
  )

let rec lemma_add_seq_map_inv (itsl: its_log) (i: I.seq_index itsl{is_blum_add (I.index itsl i)}):
  Lemma (requires True)
        (ensures (add_seq_map_inv itsl (add_seq_map itsl i) = i))
        (decreases (I.length itsl))
        [SMTPat (add_seq_map itsl i)] = 
  let n = I.length itsl in
  let s = ts_add_seq itsl in
  if n = 0 then ()
  else 
    let itsl' = I.prefix itsl (n - 1) in
    let s' = ts_add_seq itsl' in
    if i = n - 1 then ()
    else 
      lemma_add_seq_map_inv itsl' i  

let lemma_add_elem_correct (itsl: its_log) (i: I.seq_index itsl):
  Lemma (requires (is_blum_add (I.index itsl i)))
        (ensures (contains (blum_add_elem (I.index itsl i)) (ts_add_set itsl))) = 
  let sa = ts_add_seq itsl in        
  let j = add_seq_map itsl i in
  //assert(S.index sa j = blum_add_elem (I.index itsl i));
  lemma_seq_elem sa j

let rec ts_add_seq_key_aux (itsl: its_log) (k:key): 
  Tot (seq ms_hashfn_dom) 
  (decreases (I.length itsl)) = 
  let n = I.length itsl in
  if n = 0 then S.empty #ms_hashfn_dom
  else
    let itsl' = I.prefix itsl (n - 1) in
    let s' = ts_add_seq_key_aux itsl' k in
    let e = I.index itsl (n - 1) in
    if is_blum_add e && key_of e = k  then 
      SA.append1 s' (blum_add_elem e)
    else
      s'

let ts_add_seq_key (itsl: its_log) (k:key): seq ms_hashfn_dom =
  ts_add_seq_key_aux itsl k

(* into mapping from ts add seq to global add seq *)
let global_to_ts_addset_map_aux (itsl: its_log) (i: SA.seq_index (g_add_seq (g_vlog_of itsl))):
  Tot (j: SA.seq_index (ts_add_seq itsl) 
       {
          S.index (g_add_seq (g_vlog_of itsl)) i = 
          S.index (ts_add_seq itsl) j
       }) =          
  let gl = g_vlog_of itsl in
  let gs = g_add_seq gl in
  let ii = VG.add_set_map_inv gl i in
  let ts = ts_add_seq itsl in
  let i' = s2i_map itsl ii in
  let j = add_seq_map itsl i' in
  j

let lemma_global_to_ts_addset_map_into (itsl: its_log):
  Lemma (forall (i1: SA.seq_index (g_add_seq (g_vlog_of itsl))).
         forall (i2: SA.seq_index (g_add_seq (g_vlog_of itsl))).
         i1 <> i2 ==> global_to_ts_addset_map_aux itsl i1 <> 
                    global_to_ts_addset_map_aux itsl i2) = 
  let gl = g_vlog_of itsl in
  let gs = g_add_seq gl in
  
  let aux (i1 i2: SA.seq_index gs):
    Lemma (requires True)
          (ensures (i1 <> i2 ==> global_to_ts_addset_map_aux itsl i1 <>
                               global_to_ts_addset_map_aux itsl i2)) = ()    
  in  
  forall_intro_2 aux

let global_to_ts_addset_map (itsl: its_log):
  into_smap (g_add_seq (g_vlog_of itsl)) 
       (ts_add_seq itsl) = 
  lemma_global_to_ts_addset_map_into itsl;
  global_to_ts_addset_map_aux itsl

let ts_to_global_addset_map_aux (itsl: its_log) (j: SA.seq_index (ts_add_seq itsl)):
  Tot (i: SA.seq_index (g_add_seq (g_vlog_of itsl))
       {
          S.index (g_add_seq (g_vlog_of itsl)) i = 
          S.index (ts_add_seq itsl) j
       }) = 
 let gl = g_vlog_of itsl in
 let gs = g_add_seq gl in
 let ts = ts_add_seq itsl in
 let i' = add_seq_map_inv itsl j in  
 let ii = i2s_map itsl i' in
 let i = VG.add_set_map gl ii in
 i

let lemma_ts_to_global_addset_map_into (itsl: its_log):
  Lemma (forall (i1: SA.seq_index (ts_add_seq itsl)).
         forall (i2: SA.seq_index (ts_add_seq itsl)).
           i1 <> i2 ==> ts_to_global_addset_map_aux itsl i1 <>
                      ts_to_global_addset_map_aux itsl i2) = 
  let gl = g_vlog_of itsl in
  let gs = g_add_seq gl in
  let ts = ts_add_seq itsl in

  let aux (i1 i2: SA.seq_index ts):
    Lemma (i1 <> i2 ==> ts_to_global_addset_map_aux itsl i1 <>
                      ts_to_global_addset_map_aux itsl i2) = ()
  in
  forall_intro_2 aux

let ts_to_global_addset_map (itsl: its_log):
  into_smap (ts_add_seq itsl)
            (g_add_seq (g_vlog_of itsl)) = 
  lemma_ts_to_global_addset_map_into itsl;
  ts_to_global_addset_map_aux itsl

let lemma_ts_add_set_correct (itsl: its_log): 
  Lemma (ts_add_set itsl == g_add_set (g_vlog_of itsl)) = 
  let gl = g_vlog_of itsl in
  let gs = g_add_seq gl in
  let ts = ts_add_seq itsl in
  
  lemma_mset_bijection gs ts (global_to_ts_addset_map itsl)
                             (ts_to_global_addset_map itsl);
  ()

let lemma_ts_add_set_key_extend (itsl: its_log {I.length itsl > 0}):
  Lemma (requires (is_blum_add (I.telem itsl)))
        (ensures (ts_add_set_key itsl (key_of (I.index itsl (I.length itsl - 1))) == 
                  add_elem (ts_add_set_key (I.prefix itsl (I.length itsl - 1))
                                           (key_of (I.index itsl (I.length itsl - 1))))
                           (blum_add_elem (I.telem itsl)))) =
  let n = I.length itsl in
  let e = I.telem itsl in
  let k = key_of e in
  let itsl' = I.prefix itsl (n - 1) in
  let s' = ts_add_seq_key itsl' k in
  let be = blum_add_elem e in
  lemma_add_elem s' be

let rec lemma_ts_add_set_key_contains_only_aux 
  (itsl: its_log) 
  (k: key) 
  (i:SA.seq_index (ts_add_seq_key itsl k)):
  Lemma (requires True)
        (ensures (MH.key_of (S.index (ts_add_seq_key itsl k) i) = k))
        (decreases (I.length itsl)) = 
  let n = I.length itsl in
  let itsl' = I.prefix itsl (n - 1) in
  let s' = ts_add_seq_key itsl' k in
  if i = S.length s' then ()
  else 
    lemma_ts_add_set_key_contains_only_aux itsl' k i

let some_add_elem_idx (itsl: its_log) 
  (be: ms_hashfn_dom{MS.contains be (ts_add_set itsl)}): 
  (i:(I.seq_index itsl){is_blum_add (I.index itsl i) /\
                      be = blum_add_elem (I.index itsl i)}) = 
  let s = ts_add_seq itsl in  
  (* index of element be in s *)
  let j = index_of_mselem s be in
  add_seq_map_inv itsl j

let lemma_ts_add_set_key_contains_only (itsl: its_log) (k:key) (be: ms_hashfn_dom):
  Lemma (requires (MS.contains be (ts_add_set_key itsl k)))
        (ensures (MH.key_of be = k)) = 
  let s = ts_add_seq_key itsl k in
  let j = index_of_mselem s be in  
  assert(S.index s j = be);
  lemma_ts_add_set_key_contains_only_aux itsl k j

(* get the blum evict element from an index *)
let blum_evict_elem (itsl: its_log) (i:I.seq_index itsl{is_evict_to_blum (I.index itsl i)}):
  (e:ms_hashfn_dom{MH.key_of e = key_of (I.index itsl i)}) = 
  let gl = g_vlog_of itsl in
  let ii = i2s_map itsl i in
  let (tid,j) = ii in
  let tl = VG.thread_log gl tid in
  lemma_blum_evict_elem_key tl j;  
  VG.blum_evict_elem gl ii

let lemma_index_blum_evict_prefix (itsl: its_log) (i:nat{i <= I.length itsl}) (j:nat{j < i}):
  Lemma (requires (is_evict_to_blum (I.index itsl j)))
        (ensures (blum_evict_elem itsl j = blum_evict_elem (I.prefix itsl i) j)) =
  let gl = g_vlog_of itsl in
  let (t,j') = i2s_map itsl j in
  let tl = thread_log gl t in  
  assert(blum_evict_elem itsl j = VT.blum_evict_elem tl j');
  
  let itsl' = I.prefix itsl i in
  let gl' = g_vlog_of itsl' in
  let tl' = thread_log gl' t in
  lemma_i2s_map_prefix itsl i j;
  //assert(i2s_map itsl j = i2s_map itsl' j);
  //assert(blum_evict_elem itsl' j = VT.blum_evict_elem tl' j');
  lemma_prefix_interleaving itsl i t;
  //assert(tl' = VT.prefix tl (VT.length tl'));
  lemma_blum_evict_elem_prefix tl (VT.length tl') j'

let rec ts_evict_seq_aux (itsl: its_log): 
  Tot (seq ms_hashfn_dom)
  (decreases (I.length itsl)) = 
  let n = I.length itsl in
  if n = 0 then S.empty #ms_hashfn_dom
  else
    let itsl' = I.prefix itsl (n - 1) in
    let s' = ts_evict_seq_aux itsl' in
    let e = I.index itsl (n - 1) in
    if is_evict_to_blum e then
      SA.append1 s' (blum_evict_elem itsl (n - 1))
    else
      s'

(* sequence of evicts in time sequence log *)
let ts_evict_seq = ts_evict_seq_aux

let rec ts_evict_seq_key_aux (itsl: its_log) (k:key): 
  Tot (seq ms_hashfn_dom)
  (decreases (I.length itsl)) = 
  let n = I.length itsl in
  if n = 0 then S.empty #ms_hashfn_dom
  else
    let itsl' = I.prefix itsl (n - 1) in
    let s' = ts_evict_seq_key_aux itsl' k in
    let e = I.index itsl (n - 1) in
    if is_evict_to_blum e && key_of e = k then
      SA.append1 s' (blum_evict_elem itsl (n - 1))
    else
      s'  

(* the evict sequence restricted to key k *)
let ts_evict_seq_key = ts_evict_seq_key_aux

let rec evict_seq_map (itsl: its_log) (i:I.seq_index itsl {is_evict_to_blum (I.index itsl i)}):
  Tot (j:SA.seq_index (ts_evict_seq itsl){S.index (ts_evict_seq itsl) j = 
                                          blum_evict_elem itsl i}) 
  (decreases (I.length itsl)) = 
  let n = I.length itsl in
  let itsl' = I.prefix itsl (n - 1) in
  let s' = ts_evict_seq itsl' in
  if i = n - 1 then S.length s'
  else evict_seq_map itsl' i

let rec evict_seq_inv_map (itsl: its_log) (j:SA.seq_index (ts_evict_seq itsl)):
  Tot (i:I.seq_index itsl {is_evict_to_blum (I.index itsl i) /\
                           evict_seq_map itsl i = j}) 
  (decreases (I.length itsl)) = 
  let n = I.length itsl in
  let itsl' = I.prefix itsl (n - 1) in
  let s' = ts_evict_seq itsl' in
  if j = S.length s' then n - 1
  else
    evict_seq_inv_map itsl' j

let rec lemma_evict_seq_inv_map (itsl: its_log) (i:I.seq_index itsl {is_evict_to_blum (I.index itsl i)}):
  Lemma (requires True)
        (ensures (evict_seq_inv_map itsl (evict_seq_map itsl i) = i))
        (decreases (I.length itsl))
        [SMTPat (evict_seq_map itsl i)] = 
  let n = I.length itsl in
  let itsl' = I.prefix itsl (n - 1) in
  let s' = ts_evict_seq itsl' in
  if i = n - 1 then ()
  else 
    lemma_evict_seq_inv_map itsl' i

let global_to_ts_evictseq_map_aux (itsl: its_log) (i: SA.seq_index (g_evict_seq (g_vlog_of itsl))):
  Tot (j: SA.seq_index (ts_evict_seq itsl)
       {
         S.index (g_evict_seq (g_vlog_of itsl)) i =
         S.index (ts_evict_seq itsl) j
       }) = 
  let gl = g_vlog_of itsl in
  let gs = g_evict_seq gl in
  let ii = VG.evict_seq_map_inv gl i in
  let ts = ts_add_seq itsl in
  let i' = s2i_map itsl ii in
  let j = evict_seq_map itsl i' in
  j

let lemma_global_to_ts_evictseq_map_into (itsl: its_log):
  Lemma (forall (i1: SA.seq_index (g_evict_seq (g_vlog_of itsl))).
         forall (i2: SA.seq_index (g_evict_seq (g_vlog_of itsl))).
         i1 <> i2 ==> global_to_ts_evictseq_map_aux itsl i1 <>
                    global_to_ts_evictseq_map_aux itsl i2) = 
  let gl = g_vlog_of itsl in
  let gs = g_evict_seq gl in
  let aux (i1 i2: SA.seq_index gs):
    Lemma (requires True)
          (ensures (i1 <> i2 ==> global_to_ts_evictseq_map_aux itsl i1 <>
                               global_to_ts_evictseq_map_aux itsl i2)) = ()    
  in  
  forall_intro_2 aux                   

let global_to_ts_evictseq_map (itsl: its_log):
  into_smap (g_evict_seq (g_vlog_of itsl))
            (ts_evict_seq itsl) = 
  lemma_global_to_ts_evictseq_map_into itsl;
  global_to_ts_evictseq_map_aux itsl

let ts_to_global_evictseq_map_aux (itsl: its_log) (j:SA.seq_index (ts_evict_seq itsl)):
  Tot (i: SA.seq_index (g_evict_seq (g_vlog_of itsl))
       {
         S.index (g_evict_seq (g_vlog_of itsl)) i =
         S.index (ts_evict_seq itsl) j
       }) = 
  let gl = g_vlog_of itsl in       
  let gs = g_evict_seq gl in
  let ts = ts_evict_seq itsl in
  let i' = evict_seq_inv_map itsl j in
  let ii = i2s_map itsl i' in
  let i = VG.evict_seq_map gl ii in
  i

let lemma_ts_to_global_evictseq_map_into (itsl: its_log):
  Lemma (forall (i1: SA.seq_index (ts_evict_seq itsl)).
         forall (i2: SA.seq_index (ts_evict_seq itsl)).
         i1 <> i2 ==> ts_to_global_evictseq_map_aux itsl i1 <>
                    ts_to_global_evictseq_map_aux itsl i2) = 
  let ts = ts_evict_seq itsl in

  let aux (i1 i2: SA.seq_index ts):
    Lemma (i1 <> i2 ==> ts_to_global_evictseq_map_aux itsl i1 <>
                      ts_to_global_evictseq_map_aux itsl i2) = ()
  in                      
  forall_intro_2 aux

let ts_to_global_evictseq_map (itsl: its_log):
  into_smap (ts_evict_seq itsl)
            (g_evict_seq (g_vlog_of itsl)) = 
  lemma_ts_to_global_evictseq_map_into itsl;
  ts_to_global_evictseq_map_aux itsl

(* the blum evicts in time sequenced log should be the same as global evict set *)
let lemma_ts_evict_set_correct (itsl: its_log):
  Lemma (ts_evict_set itsl == g_evict_set (g_vlog_of itsl)) = 
  let gl = g_vlog_of itsl in
  let gs = g_evict_seq gl in
  let ts = ts_evict_seq itsl in
  
  lemma_mset_bijection gs ts (global_to_ts_evictseq_map itsl)
                             (ts_to_global_evictseq_map itsl)
                             
(* if the tail element is not an evict, the evict set is the same as the evict 
 * set of the length - 1 prefix 
 *)
let lemma_ts_evict_set_key_extend2 (itsl: its_log {I.length itsl > 0}):
  Lemma (requires (not (is_evict_to_blum (I.index itsl (I.length itsl - 1)))))
        (ensures (ts_evict_set_key itsl (key_of (I.index itsl (I.length itsl - 1))) == 
                  ts_evict_set_key (I.prefix itsl (I.length itsl - 1))
                                           (key_of (I.index itsl (I.length itsl - 1))))) = ()

(* since evict_set is a pure set (not a multiset) we can identify the unique index 
 * for each element of the set *)
let index_blum_evict (itsl: its_log) (e: ms_hashfn_dom {contains e (ts_evict_set itsl)}):
  (i:I.seq_index itsl{is_evict_to_blum (I.index itsl i) /\ 
                      blum_evict_elem itsl i = e}) = 
  let esq = ts_evict_seq itsl in
  let est = ts_evict_set itsl in
  let j = index_of_mselem esq e in
  assert(S.index esq j = e);
  evict_seq_inv_map itsl j

(* the clock of an evict entry is the timestamp in the corresponding blum element *)
let lemma_evict_clock (itsl: its_log) (i:I.seq_index itsl{is_evict_to_blum (I.index itsl i)}):
  Lemma (TL.clock itsl i = MH.timestamp_of (blum_evict_elem itsl i)) = admit()

(* the clock of a blum add entry is >= timestamp in the corresponding blum element *)
let lemma_add_clock (itsl: its_log) (i: I.seq_index itsl{is_blum_add (I.index itsl i)}):
  Lemma (MH.timestamp_of (blum_add_elem (I.index itsl i)) `ts_lt` TL.clock itsl i) = admit()

(* if the blum add occurs in the blum evict set, its index is earlier *)
let lemma_evict_before_add (itsl: its_log) (i:I.seq_index itsl{is_blum_add (I.index itsl i)}):
  Lemma (requires True)
        (ensures (not (contains (blum_add_elem (I.index itsl i)) (ts_evict_set itsl)) \/
                  index_blum_evict itsl (blum_add_elem (I.index itsl i)) < i)) = 
  let be = blum_add_elem (I.index itsl i) in                  
  let evt_set = ts_evict_set itsl in
  let add_set = ts_add_set itsl in
  lemma_add_clock itsl i;
  if contains be evt_set then (
    let j = index_blum_evict itsl be in
    lemma_evict_clock itsl j;
    lemma_clock_ordering itsl j i
  )
  else ()

(* the evict set of a prefix is a prefix of the evict set *)
let lemma_prefix_evict_seq (itsl: its_log) (i:nat{i < I.length itsl}):
  Lemma (requires True)
        (ensures (SA.is_prefix (ts_evict_seq itsl) (ts_evict_seq (I.prefix itsl i))))
        (decreases (I.length itsl)) = 
          
  admit()

let lemma_evict_seq_map_prefix (itsl: its_log) (i: nat{i< I.length itsl}) (j:nat):
  Lemma (requires (j < i /\
                   is_evict_to_blum (I.index itsl j)))
        (ensures (evict_seq_map itsl j = evict_seq_map (I.prefix itsl i) j)) = admit()

(* a slightly different version of of the previous lemma - the count of an add element 
 * in the evict set is the same in the prefix as the full sequence *)
let lemma_evict_before_add2 (itsl: its_log) (i:I.seq_index itsl{is_blum_add (I.index itsl i)}):
   Lemma (requires True)
         (ensures (MS.mem (blum_add_elem (I.index itsl i)) (ts_evict_set itsl) =
                   MS.mem (blum_add_elem (I.index itsl i)) (ts_evict_set (I.prefix itsl i)))) = 
   let be = blum_add_elem (I.index itsl i) in
   let evt_seq = ts_evict_seq itsl in
   let evt_set = ts_evict_set itsl in
   let itsl' = I.prefix itsl i in   
   let evt_seq' = ts_evict_seq itsl' in
   let evt_set' = ts_evict_set itsl' in

   lemma_prefix_evict_seq itsl i;
   //assert(is_prefix evt_seq evt_seq');

   lemma_prefix_mem evt_seq evt_seq' be;
   //assert(mem be evt_set' <= mem be evt_set);

   if mem be evt_set' < mem be evt_set then (
     (* since evt_set is a set ... *)
     g_evict_set_is_set (g_vlog_of itsl);
     lemma_ts_evict_set_correct itsl;
     //assert(is_set evt_set);

     (* the following mem facts must be true *)
     //assert(mem be evt_set = 1);
     //assert(mem be evt_set' = 0);

     (* however from previous lemma, it follows that evt_set' should contain be, a contradiction *)
     lemma_evict_before_add itsl i;
     let j = index_blum_evict itsl be in
     //assert(j < i);

     lemma_evict_seq_map_prefix itsl i j;
     let j' = evict_seq_map itsl' j in
     //assert(S.index evt_seq' j' = be);

     lemma_seq_elem evt_seq' j';
     //assert(contains be evt_set');
     
     ()
   )
   else ()

let lemma_evict_before_add3 (itsl: its_log) (i: I.seq_index itsl) (j:I.seq_index itsl):
  Lemma (requires (is_blum_add (I.index itsl i) /\
                   is_evict_to_blum (I.index itsl j) /\
                   blum_add_elem (I.index itsl i) = blum_evict_elem itsl j))
        (ensures (j < i)) = 
  let be = blum_add_elem (I.index itsl i) in        
  let evt_seq = ts_evict_seq itsl in
  let evt_set = ts_evict_set itsl in
  let add_seq = ts_add_seq itsl in
  let add_set = ts_add_set itsl in
  
  let j1 = evict_seq_map itsl j in  
  //assert(S.index evt_seq j1 = be);

  (* evict set contains be *)
  lemma_seq_elem evt_seq j1;
  assert(contains be evt_set);

  
  let j' = index_blum_evict itsl be in
  lemma_evict_before_add itsl i;
  assert(j' < i);

  if j' <> j then (
    let j2 = evict_seq_map itsl j' in
    assert(j1 <> j2);

    lemma_seq_elem2 evt_seq j1 j2;
    assert(mem be evt_set >= 2);

    (* this is a contradiction since evt_set is a set *)
    g_evict_set_is_set (g_vlog_of itsl);
    lemma_ts_evict_set_correct itsl
  )
  else ()

(* for an eac ts log, if the eac state of a key k is instore, the count of blum evicts 
 * is the same of blum adds for that key *)
let lemma_evict_add_count_same (itsl: TL.eac_log) (k:key):
  Lemma (requires (TL.is_eac_state_instore itsl k))
        (ensures (MS.size (ts_add_set_key itsl k) = MS.size (ts_evict_set_key itsl k))) = admit()

(* for an eac ts log, if the eac state of a key k is evicted to merkle, the count of blum evicts 
 * is the same of blum adds for that key *)
let lemma_evict_add_count_same_evictedm (itsl: TL.eac_log) (k:key):
  Lemma (requires (is_eac_state_evicted_merkle itsl k))
        (ensures (MS.size (ts_add_set_key itsl k) = MS.size (ts_evict_set_key itsl k))) = admit()

let lemma_mem_key_add_set_same (itsl: its_log) (be: ms_hashfn_dom):
  Lemma (mem be (ts_add_set itsl) = mem be (ts_add_set_key itsl (MH.key_of be))) = admit()

let lemma_mem_key_evict_set_same (itsl: its_log) (be: ms_hashfn_dom):
  Lemma (mem be (ts_evict_set itsl) = mem be (ts_evict_set_key itsl (MH.key_of be))) =admit()

(* the count of an element can only decrease in a prefix of itsl *)
let lemma_mem_monotonic (be:ms_hashfn_dom) (itsl: its_log) (i:nat{i <= I.length itsl}):
  Lemma (mem be (ts_evict_set itsl) >= mem be (ts_evict_set (I.prefix itsl i)) /\
         mem be (ts_add_set itsl) >= mem be (ts_add_set (I.prefix itsl i))) = admit()

(* the next add of a blum evict is a blum add of the same "element" *)
let lemma_blum_evict_add_same (itsl: TL.eac_log) (i:I.seq_index itsl):
  Lemma (requires (is_evict_to_blum (I.index itsl i) /\
                   TL.has_next_add_of_key itsl i (key_of (I.index itsl i))))
        (ensures (is_blum_add (I.index itsl (TL.next_add_of_key itsl i (key_of (I.index itsl i)))) /\
                  blum_evict_elem itsl i =                                   
                  blum_add_elem (I.index itsl (TL.next_add_of_key itsl i (key_of (I.index itsl i)))))) = admit()

(* when the eac store is evicted, there exists a previous evict *)
let lemma_eac_evicted_blum_implies_previous_evict (itsl: its_log) (k:key):
  Lemma (requires (is_eac_state_evicted_blum itsl k))
        (ensures (has_some_entry_of_key itsl k /\
                  is_evict_to_blum (I.index itsl (last_idx_of_key itsl k)) /\
                  blum_evict_elem itsl (last_idx_of_key itsl k) = 
                  to_blum_elem (eac_state_of_key itsl k) k)) = admit()

(* if we provide two indexes having the same add element then the membership of the element in the 
 * add set is at least two *)
let lemma_add_set_mem (itsl: its_log) (i: I.seq_index itsl) (j:I.seq_index itsl{j <> i}):
  Lemma (requires (is_blum_add (I.index itsl i) /\
                   is_blum_add (I.index itsl j) /\
                   blum_add_elem (I.index itsl i) = blum_add_elem (I.index itsl j)))
        (ensures (MS.mem (blum_add_elem (I.index itsl i)) (ts_add_set itsl) >= 2)) = admit()
