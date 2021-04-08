module Veritas.Intermediate.Logs

let consistent_log_hprefix_consistent #vcfg (init_map: slot_state_map vcfg) (l:logS vcfg):
  Lemma (requires (consistent_log init_map l /\ length l > 0))
        (ensures (consistent_log init_map (prefix l (length l - 1))))
        [SMTPat (consistent_log init_map l)]
        =
  let n = length l in
  let l' = prefix l (n - 1) in

  let aux s: Lemma
    (ensures (slot_state_trans_closure s l' (init_map s) <> None))
    [SMTPat (slot_state_trans_closure s l' (init_map s))] =
    if slot_state_trans_closure s l' (init_map s) = None then
      assert(slot_state_trans_closure s l (init_map s) = None)
    else ()
  in
  ()

let rec consistent_log_prefix_consistent #vcfg (init_map: slot_state_map vcfg) (l:logS vcfg) (i:nat{i <= length l}):
  Lemma (requires (consistent_log init_map l))
        (ensures (consistent_log init_map (prefix l i)))
        (decreases (length l))
        [SMTPat (consistent_log init_map (prefix l i))]
        =
  let n = length l in
  if i = n then ()
  else
    let l' = prefix l (n - 1) in
    consistent_log_hprefix_consistent init_map l;
    consistent_log_prefix_consistent init_map l' i

let lemma_consistent_log_prefix_consistent (#vcfg:_) (init_map: slot_state_map vcfg) (l:logS vcfg) (i:nat{i <= length l}):
  Lemma (requires (consistent_log init_map l))
        (ensures (consistent_log init_map (prefix l i))) = consistent_log_prefix_consistent init_map l i

let consistent_log_last_entry_valid #vcfg (init_map: slot_state_map vcfg) (l: logS vcfg):
  Lemma (requires (consistent_log init_map l /\ length l > 0))
        (ensures (let n = length l in
                  let e = index l (n - 1) in
                  let l' = prefix l (n- 1) in
                  let ssm' = to_slot_state_map init_map l' in
                  valid_logS_entry ssm' e))
        [SMTPat (consistent_log init_map l)]
                  =
  let n = length l in
  let e = index l (n - 1) in
  let l' = prefix l (n- 1) in
  let ssm' = to_slot_state_map init_map l' in

  if valid_logS_entry ssm' e then ()
  else
    match e with
    | Get_S s k _
    | Put_S s k _ ->
      assert(is_free ssm' s \/ assoc_key ssm' s <> k);
      assert(slot_state_trans_closure s l (init_map s) = None);
      ()
    | AddM_S s (k,_) s' ->
      assert(is_assoc ssm' s \/ is_free ssm' s');
      if is_assoc ssm' s then
        assert(slot_state_trans_closure s l (init_map s) = None)
      else
        assert(slot_state_trans_closure s' l (init_map s') = None)
    | AddB_S s (k,_) _ _ ->
      assert(is_assoc ssm' s);
      assert(slot_state_trans_closure s l (init_map s) = None)
    | EvictM_S s s' ->
      assert(is_free ssm' s \/ is_free ssm' s');
      if is_free ssm' s then
        assert(slot_state_trans_closure s l (init_map s) = None)
      else
        assert(slot_state_trans_closure s' l (init_map s') = None)
    | EvictB_S s _ ->
      assert(slot_state_trans_closure s l (init_map s) = None)
    | EvictBM_S s s' _ ->
      if is_free ssm' s then
        assert(slot_state_trans_closure s l (init_map s) = None)
      else
        assert(slot_state_trans_closure s' l (init_map s') = None)

let rec consistent_log_all_entries_valid
  (#vcfg:_) (init_map: slot_state_map vcfg) (l:logS vcfg{consistent_log init_map l}) (i:seq_index l):
  Lemma (ensures (let l' = prefix l i in
                  lemma_consistent_log_prefix_consistent init_map l i;
                  let ssm' = to_slot_state_map init_map l' in
                  valid_logS_entry ssm' (index l i)))
        (decreases (length l))
  =
  let n = length l in
  if i = n - 1 then
    consistent_log_last_entry_valid init_map l
  else
    consistent_log_all_entries_valid init_map (prefix l (n - 1)) i

let rec to_logk_aux (#vcfg:_) (init_map: slot_state_map vcfg) (l:logS vcfg{consistent_log init_map l}):
  Tot (logK)
  (decreases (length l)) =
  let n = length l in
  if n = 0 then Seq.empty #Spec.vlog_entry
  else
    let l' = prefix l (n - 1) in
    let e = index l (n - 1) in
    //consistent_log_hprefix_consistent init_map l;
    let lk' = to_logk_aux init_map l' in
    let ssm' = to_slot_state_map init_map l' in
    //consistent_log_last_entry_valid init_map l;
    assert(valid_logS_entry ssm' e);
    let ek = to_logK_entry ssm' e in
    append1 lk' ek

let to_logk (#vcfg:_) (init_map: slot_state_map vcfg) (l:logS vcfg{consistent_log init_map l}): logK =
  to_logk_aux init_map l

let rec lemma_to_logk_length_aux (#vcfg:_) (init_map: slot_state_map vcfg) (l:logS vcfg{consistent_log init_map l}):
  Lemma (ensures (length (to_logk init_map l) = length l))
        (decreases (length l))
  =
  let n = length l in
  if n = 0 then ()
  else
    let l' = prefix l (n - 1) in
    lemma_to_logk_length_aux init_map l'

let lemma_to_logk_length (#vcfg:_) (init_map: slot_state_map vcfg) (l:logS vcfg{consistent_log init_map l}):
  Lemma (ensures (length (to_logk init_map l) = length l))
  = lemma_to_logk_length_aux init_map l

let lemma_all_entries_valid (#vcfg:_) (init_map: slot_state_map vcfg) (l:logS vcfg{consistent_log init_map l}) (i:seq_index l):
  Lemma (ensures (let l' = prefix l i in
                  lemma_consistent_log_prefix_consistent init_map l i;
                  let ssm' = to_slot_state_map init_map l' in
                  valid_logS_entry ssm' (index l i)))
  = consistent_log_all_entries_valid init_map l i

let rec lemma_to_logk_index_aux (#vcfg:_) (init_map: slot_state_map vcfg) (l:logS _{consistent_log init_map l}) (i:seq_index l):
  Lemma (ensures (let lk = to_logk init_map l in
                  let l' = prefix l i in
                  lemma_consistent_log_prefix_consistent init_map l i;
                  let ssm' = to_slot_state_map init_map l' in
                  lemma_all_entries_valid init_map l i;
                  index lk i = to_logK_entry ssm' (index l i)))
        (decreases (length l))
  =
  let n = length l in
  if n = 0 then ()
  else if i = n - 1 then ()
  else
    lemma_to_logk_index_aux init_map (prefix l (n - 1)) i

let lemma_to_logk_index (#vcfg:_) (init_map: slot_state_map vcfg) (l:logS _{consistent_log init_map l}) (i:seq_index l):
  Lemma (ensures (let lk = to_logk init_map l in
                  let l' = prefix l i in
                  lemma_consistent_log_prefix_consistent init_map l i;
                  let ssm' = to_slot_state_map init_map l' in
                  lemma_all_entries_valid init_map l i;
                  index lk i = to_logK_entry ssm' (index l i)))
  = lemma_to_logk_index_aux init_map l i
