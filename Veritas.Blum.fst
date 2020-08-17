module Veritas.Blum

open FStar.Seq
open Veritas.MultiSet
open Veritas.MultiSetHash
open Veritas.SeqAux
open Veritas.Verifier
open Veritas.Verifier.CorrectDefs

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

(* the thread id of a verifier remains unchanged *)
let rec lemma_thread_id (il:t_verifiable_log):
  Lemma (requires True)
        (ensures (thread_id (t_verify (fst il) (snd il)) = (fst il)))
        (decreases (tv_length il)) = 
  let (id,l) = il in
  let n = length l in
  if n = 0 then ()
  else
    lemma_thread_id (id, hprefix l)

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
