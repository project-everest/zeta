module Veritas.State

let lemma_extend_rw_consistency_put (s:seq state_op{length s > 0}):
  Lemma (requires (Put? (index s (length s - 1)) /\ 
                   rw_consistent (prefix s (length s - 1))))
        (ensures (rw_consistent s)) = 
  let n = length s in
  let s' = prefix s (n - 1) in
  let e = index s (n - 1) in
  let aux (i:seq_index s):
    Lemma (requires is_get_idx s i)
          (ensures value_of_idx s i = last_put_value_or_null (prefix s i) (key_of_idx s i))
          [SMTPat (is_get_idx s i)] = 
    if i < n - 1 then (
      assert(rw_consistent_idx s' i);
      ()
    )
    else ()
  in
  ()

(* computational version of rw_consistency *)
let rec eval_rw_consistency_aux (s: seq (state_op)): 
  Tot (r:(bool * nat){(fst r <==> rw_consistent s) /\
                     (~(rw_consistent s) ==> (snd r < length s /\ 
                                             rw_inconsistent_idx s (snd r) /\
                                             rw_consistent (prefix s (snd r)))
                                                                     
                     )})
  (decreases (length s)) = 
  let n = length s in
  if n = 0 then (true, 0)
  else 
    let s' = prefix s (n - 1) in
    let e = index s (n - 1) in
    let (c',i') = eval_rw_consistency_aux s' in
    if c' then
      admit()
    else 
      admit()

let eval_rw_consistency = eval_rw_consistency_aux
