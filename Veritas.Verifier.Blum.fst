module Veritas.Verifier.Blum

open Veritas.EAC

(* get the add seq of a log *)
let rec add_seq (il:t_verifiable_log): 
  Tot (seq ms_hashfn_dom)
  (decreases (tv_length il)) =
  let (id,l) = il in
  let n = length l in  
  if n = 0 then 
    Seq.empty #ms_hashfn_dom
  else 
    let l' = hprefix l in
    let e = telem l in
    match e with
    | AddB r t j -> append1 (add_seq (id, l')) (MHDom r t j)
    | _ ->  add_seq (id,l')

(* get the add multi-set of a log *)
let add_set (il:t_verifiable_log): mset ms_hashfn_dom = 
  seq2mset (add_seq il)

(* 
 * the hadd hash value maintained by a verifier thread is the multiset hash 
 * of its add_set 
 *)
let rec lemma_hadd_add_set (il:t_verifiable_log):
  Lemma (requires True)
        (ensures (thread_hadd (t_verify (fst il) (snd il)) = ms_hashfn (add_seq il))) 
        (decreases (tv_length il)) =
  let (id,l) = il in
  let n = length l in
  let st = t_verify id l in
  if n = 0 then 
    lemma_hashfn_empty()  
  else (
    let l' = hprefix l in
    let e = telem l in
    lemma_hadd_add_set (id, l');
    match e with
    | AddB r t j -> 
           lemma_hashfn_app (add_seq (id, l')) (MHDom r t j)
    | _ -> ()
  )

(* concatenation of all local add-seq *)
let g_add_seq (gl: g_verifiable_log): seq (ms_hashfn_dom) = 
  let gl' = g_verifiable_refine gl in
  (* sequence of local add_sequences *)
  let l_adds = map add_seq gl' in
  reduce (Seq.empty #ms_hashfn_dom) append l_adds

(* the hadd that the verifier computes is the multiset hash of all the adds *)
let lemma_g_hadd_correct (gl: g_verifiable_log):
  Lemma (g_hadd gl = ms_hashfn (g_add_seq gl)) = admit()

(* sequence of versioned records evicted from a verifier *)
let rec evict_seq (il:t_verifiable_log):
  Tot (seq ms_hashfn_dom)
  (decreases (tv_length il)) = 
  let (id,l) = il in
  let n = length l in  
  if n = 0 then 
    Seq.empty #ms_hashfn_dom
  else 
    let (_,l') = tv_prefix il (n - 1) in
    let e = telem l in
    let vs' = t_verify id l' in
    let st' = thread_store vs' in
    match e with
    | EvictB k t -> 
      let v = stored_value st' k in 
      append1 (evict_seq (id, l')) (MHDom (k,v) t id)
    | EvictBM k k' t -> 
      let v = stored_value st' k in 
      append1 (evict_seq (id, l')) (MHDom (k,v) t id)    
    | _ -> evict_seq (id, l')

(* evict multiset of a verifier *)
let evict_set (il:t_verifiable_log): mset ms_hashfn_dom =
  seq2mset (evict_seq il)

(* a single sequence containing all the blum evicts *)
let g_evict_seq (gl: g_verifiable_log): seq ms_hashfn_dom = 
  let gl' = g_verifiable_refine gl in
  (* sequence of local add_sequences *)
  let l_evicts = map evict_seq gl' in
  reduce (Seq.empty #ms_hashfn_dom) append l_evicts 

let g_evict_set_is_set (gl: g_verifiable_log): 
  Lemma (is_set (g_evict_set gl)) = admit()

let lemma_ghevict_correct (gl: g_verifiable_log):
  Lemma (g_hevict gl = ms_hashfn (g_evict_seq gl)) = admit()

let rec lemma_hevict_evict_set (il:t_verifiable_log):
  Lemma (requires True)
        (ensures (thread_hevict (t_verify (fst il) (snd il)) = ms_hashfn (evict_seq il)))
        (decreases (tv_length il)) =
  let (id, l) = il in
  let n = length l in
  if n = 0 then lemma_hashfn_empty()
  else (
    let l' = hprefix l in
    let e = telem l in
    let vs' = t_verify id l' in
    let st' = thread_store vs' in    
    lemma_hevict_evict_set (id, l');
    lemma_thread_id (id, l');
    match e with
    | EvictB k t -> 
      let v = stored_value st' k in
      lemma_hashfn_app (evict_seq (id, l')) (MHDom (k,v) t id)
    | EvictBM k _ t -> 
      let v = stored_value st' k in
      lemma_hashfn_app (evict_seq (id, l')) (MHDom (k,v) t id)
    | _ -> ()
  )

(* sequence of blum adds in a time sequenced log *)
let ts_add_seq (#n:pos) (itsl: its_log n): seq ms_hashfn_dom =
  map blum_add_elem (filter_refine is_blum_add itsl)

let ts_add_seq_key (#n:pos) (itsl: its_log n) (k:key): seq ms_hashfn_dom
 = admit()

let lemma_ts_add_set_correct (#n:pos) (itsl: its_log n): 
  Lemma (ts_add_set itsl == g_add_set (partition_idx_seq itsl)) = admit()

let is_blum_evict (#n:pos) (itsl: its_log n) (i: seq_index itsl): bool = 
  let (e,_) = index itsl i in
  match e with
  | EvictB _ _ -> true
  | EvictBM _ _ _ -> true
  | _ -> false

let blum_evict_elem (#p:pos) (itsl: its_log p) (i:seq_index itsl{is_blum_evict itsl i}):
  (e:ms_hashfn_dom{M.key_of e = TL.key_of itsl i}) =
  let (e,id) = index itsl i in
  let tsle = time_seq_ext itsl in
  assert(project_seq itsl = to_vlog tsle);
  lemma_unzip_index itsl i;
  assert(to_vlog_entry (index tsle i) = e);
  match e with
  | EvictB k t -> 
    let v = Evict?.v (index tsle i) in
    MHDom (k,v) t id
  | EvictBM k _ t -> 
    let v = Evict?.v (index tsle i) in
    MHDom (k,v) t id
 
let rec ts_evict_seq_aux (#n:pos) (itsl: its_log n): Tot (seq ms_hashfn_dom) 
  (decreases (length itsl)) =
  let m = length itsl in 
  if m = 0 then Seq.empty #ms_hashfn_dom
  else if is_blum_evict itsl (m - 1) then
    append1 (ts_evict_seq_aux (its_prefix itsl (m - 1))) (blum_evict_elem itsl (m - 1))   
  else
    ts_evict_seq_aux (its_prefix itsl (m - 1))

let ts_evict_seq = ts_evict_seq_aux

let ts_evict_seq_key (#n:pos) (itsl: its_log n) (k:key): seq ms_hashfn_dom = 
  admit()

let lemma_ts_evict_set_correct (#n:pos) (itsl: its_log n):
  Lemma (ts_evict_set itsl == g_evict_set (partition_idx_seq itsl)) = admit()

let index_blum_evict (#p:pos) (itsl: its_log p) (e: ms_hashfn_dom {contains e (ts_evict_set itsl)}):
  (i:seq_index itsl{is_blum_evict itsl i /\ 
                    blum_evict_elem itsl i = e}) = admit()

let lemma_evict_before_add (#p:pos) (itsl: its_log p) (i:seq_index itsl{is_blum_add (index itsl i)}):
  Lemma (requires True)
        (ensures (not (contains (blum_add_elem (index itsl i)) (ts_evict_set itsl)) \/
                  index_blum_evict itsl (blum_add_elem (index itsl i)) < i)) = admit()
