module Veritas.SeqMachine

open FStar.Seq
open Veritas.SeqAux

let lemma_empty_seq_valid (sm: seq_machine):
  Lemma (valid sm (empty #(elem_type sm))) =
  lemma_reduce_empty (init_state sm) (trans_fn sm)

let lemma_valid_prefix (sm: seq_machine) (s: (seq (elem_type sm)){valid sm s}) (i:nat{i <= length s}):
  Lemma (valid sm (prefix s i)) =
  let si = prefix s i in
  if valid sm si then ()
  else (
    lemma_reduce_prefix (init_state sm) (trans_fn sm) s i;
    lemma_reduce_identity (fail_state sm) (trans_fn sm) (suffix s (length s - i))
  )

let rec max_valid_prefix_aux (sm: seq_machine) (s: seq (elem_type sm))
  : Tot (i:nat{i <= length s /\
              valid sm (prefix s i) /\
              (i < length s ==> not (valid sm (prefix s (i + 1))))
              })
    (decreases (length s)) =
  lemma_empty_seq_valid sm;
  lemma_prefix0_empty s;
  let n = length s in
  if valid sm s then n
  else max_valid_prefix_aux sm (prefix s (n - 1))

let max_valid_prefix = max_valid_prefix_aux

let lemma_empty_seq_valid_all (psm: pseq_machine):
  Lemma (valid_all psm (empty #(elem_type_p psm))) =
  let s = empty #(elem_type_p psm) in
  let key = key_type psm in
  let sm = seq_machine_of psm in
  let pf = partn_fn psm in
  let aux(k: key):
    Lemma (requires True)
          (ensures (valid sm (partn psm k s)))
          [SMTPat (valid sm (partn psm k s))]
          =
    lemma_filter_empty (iskey pf k);
    lemma_empty_seq_valid sm
  in
  ()

let lemma_valid_all_prefix (psm: pseq_machine)
                           (s: (seq (elem_type_p psm)){valid_all psm s}) (i:nat{i <= length s}):
  Lemma (requires True)
        (ensures (valid_all psm (prefix s i)))
        (decreases (length s)) =
  let si = prefix s i in
  let key = key_type psm in
  let sm = seq_machine_of psm in
  let pf = partn_fn psm in
  let aux(k: key):
    Lemma (requires True)
          (ensures (valid sm (partn psm k si)))
          [SMTPat (valid sm (partn psm k si))]
    =
    lemma_filter_prefix (iskey pf k) s si;
    lemma_valid_prefix sm (partn psm k s) (length (partn psm k si))
  in
  ()

let lemma_valid_all_extend (psm: pseq_machine) (s: seq (elem_type_p psm)):
  Lemma (requires (length s > 0 /\
                   valid_all psm (prefix s (length s - 1)) /\
                   valid (seq_machine_of psm)
                         (partn psm (partn_fn psm (index s (length s - 1))) s)))
        (ensures (valid_all psm s)) =
  let n = length s in
  let sm = seq_machine_of psm in
  let pf = partn_fn psm in
  let key = key_type psm in
  let k' = pf (index s (n - 1)) in
  let aux(k: key):
    Lemma (requires True)
          (ensures (valid sm (partn psm k s)))
          [SMTPat (valid sm (partn psm k s))] =
    if k' = k then ()
    else lemma_filter_extend1 (iskey pf k) s    
  in
  ()

let rec max_valid_all_prefix_aux (psm: pseq_machine) (s: seq (elem_type_p psm))
  : Tot (i: nat{i <= length s /\
               valid_all psm (prefix s i) /\
               (i < length s ==>
                ~ (valid_all psm (prefix s (i + 1))))})
    (decreases (length s)) =
  let n = length s in
  let sm = seq_machine_of psm in
  let pf = partn_fn psm in
  if n = 0 then (
    lemma_prefix0_empty s;
    lemma_empty_seq_valid_all psm;
    0
  )
  else 
    let s' = prefix s (n - 1) in
    let i = max_valid_all_prefix_aux psm s' in
    if i = n - 1 then
      let e = index s (n - 1) in
      let k = pf e in
      let sk = partn psm k s in
      if valid sm sk then (
        lemma_valid_all_extend psm s;
        n
      )
      else i
    else i
  
let max_valid_all_prefix = max_valid_all_prefix_aux

let invalid (psm: pseq_machine) 
            (s: seq (elem_type_p psm)) = 
  max_valid_all_prefix psm s < length s

let invalid_key (psm: pseq_machine)
                (s: seq (elem_type_p psm){invalid psm s}) = 
  let n = length s in
  let i = max_valid_all_prefix psm s in
  let e = index s i in
  let pf = partn_fn psm in
  pf e  

let lemma_invalid_key (psm: pseq_machine)
                      (s: seq (elem_type_p psm){invalid psm s}):
  Lemma (False) = 
  let sm = seq_machine_of psm in
  let k = invalid_key psm s in
  let i = max_valid_all_prefix psm s in
  let pf = partn_fn psm in
  let s' = prefix s i in
  let s'' = prefix s (i + 1) in
  assert(valid_all psm s');
  let sk' = partn psm k s' in    
  assert(valid (seq_machine_of psm) sk');
  admit()

let valid_all_comp (psm: pseq_machine) (s: seq (elem_type_p psm)): Tot (r:bool{r <==> valid_all psm s}) = 
  let i = max_valid_all_prefix psm s in
  if i = length s then true
  else (    
    admit()
  )
