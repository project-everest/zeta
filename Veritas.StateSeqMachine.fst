module Veritas.StateSeqMachine

open FStar.Seq
open Veritas.Key
open Veritas.Record
open Veritas.State
open Veritas.SeqAux
open Veritas.SeqMachine

let has_some_put_k (s: seq state_op) =
  exists_sat_elems Put? s

let last_put_idx_k (s: seq state_op{has_some_put_k s}) =
  last_index Put? s

let last_put_value_or_null_k (s: seq state_op) =
  if has_some_put_k s then Put?.v (index s (last_put_idx_k s))
  else Null

let value_of_state (s: ssm_state{StateVal? s}) =
  match s with
  | StateVal v -> v

let lemma_last_op_get (s:seq state_op{length s > 0}):
  Lemma (requires (Get? (index s (length s - 1))))
        (ensures (last_put_value_or_null_k s = last_put_value_or_null_k (prefix s (length s - 1)))) =
  lemma_last_index_last_elem_nsat Put? s;
  if has_some_put_k s then
    lemma_last_index_prefix Put? s (length s - 1)
  else ()

let rec lemma_valid_implies_state_last_write (s: seq state_op{valid ssm_k s /\ length s > 0}):
  Lemma (requires True)
        (ensures (StateVal? (seq_machine_run ssm_k s) /\
                  value_of_state (seq_machine_run ssm_k s) = last_put_value_or_null_k s))
        (decreases (length s)) =
  let n = length s in
  lemma_notempty_implies_noninit ssm_k s;

  if Put? (index s (n - 1)) then lemma_last_index_last_elem_sat Put? s
  else lemma_last_op_get s;

  if n = 1 then
    lemma_reduce_singleton StateInit apply_state_op s
  else (
    lemma_valid_prefix ssm_k s (n - 1);
    lemma_valid_implies_state_last_write (prefix s (n - 1));
    lemma_reduce_append2 StateInit apply_state_op s
  )

let lemma_valid_implies_read_last_write (s: seq state_op{valid ssm_k s}) (i: seq_index s):
  Lemma (Get? (index s i) ==> Get?.v (index s i) = last_put_value_or_null_k (prefix s i)) =
  if not (Get? (index s i)) then ()
  else
    lemma_valid_prefix ssm_k s (i + 1);
    lemma_valid_prefix ssm_k s i;

    if i = 0 then lemma_reduce_singleton StateInit apply_state_op (prefix s (i + 1))
    else (
      lemma_notempty_implies_noninit ssm_k (prefix s i);
      lemma_valid_implies_state_last_write (prefix s i);
      lemma_reduce_append2 StateInit apply_state_op (prefix s (i + 1))
    )

let lemma_is_put_of_conj (k: data_key):
  Lemma (requires True)
        (ensures (forall x. is_put_of_key k x = conj Put? (iskey key_of k) x)) = ()

let lemma_last_put_filter (s: seq state_op) (k: data_key):
  Lemma (last_put_value_or_null s k = 
         last_put_value_or_null_k (filter (iskey key_of k) s)) = 
  lemma_exists_sat_elems_extensionality (is_put_of_key k) (conj Put? (iskey key_of k)) s;  
  if has_some_put s k then (
    lemma_last_index_extensionality (is_put_of_key k) (conj Put? (iskey key_of k)) s;
    lemma_last_idx_conj Put? (iskey key_of k) s
  )
  else (
    lemma_exists_sat_elems_extensionality (is_put_of_key k) (conj Put? (iskey key_of k)) s;
    lemma_exists_sat_conj Put? (iskey key_of k) s
  )

let lemma_valid_all_implies_rw_consistent (s: seq state_op {valid_all ssm s}):
  Lemma (rw_consistent s) = 
  let aux(i:seq_index s):
    Lemma (requires True)
          (ensures (rw_consistent_idx s i))
          [SMTPat (rw_consistent_idx s i)]
    = 
    let e = index s i in
    if Put? e then ()
    else (
      match e with Get k v ->
      let k = key_of e in
      let si = prefix s i in
      lemma_last_put_filter si k;
      let sk = partn ssm k s in            
      let j = filter_index_inv_map (iskey key_of k) s i in
      lemma_valid_implies_read_last_write sk j;
      lemma_filter_prefix_comm (iskey key_of k) s i
    )
  in  
  ()

let lemma_first_invalid_is_get (s: seq state_op{length s > 0}):
  Lemma (requires (not (valid ssm_k s) /\ valid ssm_k (prefix s (length s - 1))))
        (ensures (Get? (index s (length s - 1)) /\
                  Get?.v (index s (length s - 1)) <> 
                  last_put_value_or_null_k (prefix s (length s - 1)))) = 
  let n = length s in
  let e = index s (n - 1) in
  let s' = prefix s (n - 1) in
  let st = seq_machine_run ssm_k s in
  if n = 1 then 
    lemma_reduce_singleton StateInit apply_state_op s  
  else (
    lemma_valid_implies_state_last_write s';    
    lemma_reduce_append2 StateInit apply_state_op s
  )

let lemma_not_valid_all_implies_not_rw_consistent (s: seq state_op {~ (valid_all ssm s)}):
  Lemma (~ (rw_consistent s)) = 
  (* TODO: for some weird reason this fails if we do not declare explicit type *)
  let k:data_key = invalidating_key ssm s in
  let sk = partn ssm k s in
  let j = max_valid_prefix ssm_k sk in
  let skj = prefix sk j in
  let skj' = prefix sk (j + 1) in
  
  lemma_first_invalid_is_get skj';    
  let v = Get?.v (index sk j) in  
  assert(v <> last_put_value_or_null_k skj);
  
  let i = filter_index_map (iskey key_of k) s j in
  lemma_last_put_filter (prefix s i) k;
  lemma_filter_prefix_comm (iskey key_of k) s i

let lemma_state_sm_equiv_rw_consistent (s: seq state_op):
  Lemma (valid_all ssm s <==> rw_consistent s) = 
  if valid_all_comp ssm s then
    lemma_valid_all_implies_rw_consistent s
  else 
    lemma_not_valid_all_implies_not_rw_consistent s
  
