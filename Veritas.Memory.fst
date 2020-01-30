module Veritas.Memory

open FStar.BitVector
open FStar.Classical
open FStar.Seq
open Veritas.SeqAux


let last_write_value (l:memory_op_log) (a:addr{has_some_write l a}): Tot payload =
  written_value l (last_write_idx l a)

(* 
 * If an address has a write, then the memory of the naive verifier 
 * stores (and returns) the last write value for this address
 *)
let rec memory_is_last_write (l:memory_op_log) (m:memory) (a:addr):
  Lemma (requires (has_some_write l a && NValid? (naive_verifier m l)))
        (ensures (NValid?.m (naive_verifier m l) a = last_write_value l a))
        (decreases (length l)) =
  let n = length l in
  let f = is_write_to_addr a in
  let li = last_write_idx l a in
  if n = 0 then ()
  else if f (index l (n - 1)) then 
    if li = n - 1 then ()
    else lemma_last_index_correct1 f l (n - 1)  
  else if li = n - 1 then ()
  else (
    let l' = prefix l (n - 1) in
    lemma_prefix_index l (n - 1) li;
    lemma_last_index_correct2 f l' li;
    memory_is_last_write l' m a;    
    lemma_last_index_correct1 f l (n - 1);
    lemma_last_index_prefix f l (n - 1)
  ) 

(*
 * If we start with initial memory (all addresses null), then the 
 * memory of the naive verifier stores and returns Null for an address
 * that has no writes in the log 
 *)
let rec memory_is_null_without_write (l:memory_op_log) (a:addr):
  Lemma (requires (has_some_write l a = false /\ NValid? (naive_verifier init_memory l)))
        (ensures (NValid?.m (naive_verifier init_memory l) a = Null))
        (decreases (length l)) =
  let n = length l in
  let f = is_write_to_addr a in
  if n = 0 then ()
  else if f (index l (n - 1)) then
    lemma_last_index_correct2 f l (n - 1)
  else (
    let l' = prefix l (n - 1) in
    if has_some_write l' a then (
      lemma_prefix_index l (n - 1) (last_write_idx l' a);
      lemma_last_index_correct2 f l (last_write_idx l' a)
    )
    else
      memory_is_null_without_write l' a
  )

let rec lemma_rw_consistent_implies_correct_aux (l:rw_consistent):
  Lemma (requires (True))
        (ensures (memory_log_correct l))
        (decreases (length l))
  = 
  let n = length l in
  if n = 0 then ()
  else 
    let l' = prefix l (n - 1) in
    let o = index l (n - 1) in 
    let vs' = naive_verifier init_memory l' in
    let aux (i:log_index l'):
      Lemma(is_read_op l' i ==> 
              read_value l' i = last_write_value_or_null (prefix l' i) (address_at_idx l' i)) = 
      let pi = prefix l' i in
      let a = address_at_idx l' i in
      lemma_prefix_index l (n - 1) i;
      lemma_prefix_prefix l (n - 1) i;
      assert (pi = prefix l i);
      if is_read_op l' i then 
        if has_some_write (prefix l' i) (address_at_idx l' i) then 
          assert (has_some_write (prefix l i) (address_at_idx l i))        
        else
          assert (not (has_some_write (prefix l i) (address_at_idx l i)))      
      else ()
      in
    forall_intro aux; lemma_rw_consistent_implies_correct_aux l';
    assert (NValid? vs');
        let m' = (NValid?.m vs') in
    if Write? o then ()
    else
      let a = address_of o in
      if has_some_write l' a then (
        memory_is_last_write l' init_memory a;
        assert (is_read_op l (n - 1))
      )
      else (
        memory_is_null_without_write l' a;
        assert (is_read_op l (n - 1))
      )

let lemma_rw_consistent_implies_correct (l:rw_consistent):
    Lemma (requires (True))
        (ensures (memory_log_correct l))
        (decreases (length l)) = lemma_rw_consistent_implies_correct_aux l
