module Zeta.Intermediate.Logs

open FStar.Classical
open Zeta.SeqIdx

let all_slots_assoc_comp (#vcfg:_) (ssm: slot_state_map vcfg) (ss: seq (slot_id vcfg))
  : b:bool{b <==> all_slots_assoc ssm ss}
  = not (exists_elems_with_prop_comp (fun s -> not (is_assoc ssm s)) ss)

#push-options "--fuel 1 --ifuel 1 --query_stats"

let consistent_log_implies_hprefix_consistent (#vcfg:_) (init_map: slot_state_map vcfg) (l: logS vcfg {length l > 0})
  : Lemma (requires (consistent_log init_map l))
          (ensures (let i = length l - 1 in
                    let l' = prefix l i in
                    consistent_log init_map l'))
          [SMTPat (consistent_log init_map l)]
  = let i = length l - 1 in
    let l' = prefix l i in
    let aux(s:_)
      : Lemma (ensures (slot_state_trans_closure s l' (init_map s) <> None))
      = eliminate forall (s:slot_id vcfg). slot_state_trans_closure s l (init_map s) <> None
        with s
    in
    forall_intro aux

#pop-options

(* prefix of a consistent log is consistent *)
let rec lemma_consistent_log_prefix_consistent (#vcfg:_)
  (init_map: slot_state_map vcfg)
  (l:logS vcfg) (i:nat{i <= length l})
  : Lemma (requires (consistent_log init_map l))
          (ensures (consistent_log init_map (prefix l i)))
          (decreases (length l))
  = if i < length l then (
      let n' = length l - 1 in
      let l' = prefix l n' in
      consistent_log_implies_hprefix_consistent init_map l;
      lemma_consistent_log_prefix_consistent init_map l' i
    )

#push-options "--fuel 1 --ifuel 1 --query_stats"

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

  lemma_consistent_log_prefix_consistent init_map l (n-1);
  assert(consistent_log init_map l');

  if valid_logS_entry ssm' e then ()
  else
    match e with
    | GV.AddM r s s' ->
      assert(is_assoc ssm' s \/ is_free ssm' s');
      if is_assoc ssm' s then
        assert(slot_state_trans_closure s l (init_map s) = None)
      else
        assert(slot_state_trans_closure s' l (init_map s') = None)
    | GV.AddB r s _ _ ->
      assert(is_assoc ssm' s);
      assert(slot_state_trans_closure s l (init_map s) = None)
    | GV.EvictM s s' ->
      assert(is_free ssm' s \/ is_free ssm' s');
      if is_free ssm' s then
        assert(slot_state_trans_closure s l (init_map s) = None)
      else
        assert(slot_state_trans_closure s' l (init_map s') = None)
    | GV.EvictB s _ ->
      assert(slot_state_trans_closure s l (init_map s) = None)
    | GV.EvictBM s s' _ ->
      if is_free ssm' s then
        assert(slot_state_trans_closure s l (init_map s) = None)
      else
        assert(slot_state_trans_closure s' l (init_map s') = None)
    | GV.RunApp _ _ ss ->
      let aux (i:_)
        : Lemma (ensures (is_assoc ssm' (index ss i)))
        = let s = index ss i in
          assert(mem s ss);
          if not (is_assoc ssm' s) then
            assert(slot_state_trans_closure s l (init_map s) = None)
      in
      forall_intro aux
    | _ -> ()

#pop-options

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

let to_logk_idx
  (#vcfg:_) (init_map: slot_state_map vcfg) (l:logS vcfg{consistent_log init_map l}) (i:seq_index l)
  : logK_entry vcfg.app
  = let e = index l i in
    let l' = prefix l i in
    lemma_consistent_log_prefix_consistent init_map l i;
    let ssm' = to_slot_state_map init_map l' in
    consistent_log_all_entries_valid init_map l i;
    to_logk_entry ssm' e

let to_logk (#vcfg:_) (init_map: slot_state_map vcfg) (l:logS vcfg{consistent_log init_map l}): logK vcfg
  = init (length l) (to_logk_idx init_map l)

let lemma_to_logk_length (#vcfg:_) (init_map: slot_state_map vcfg) (l:logS vcfg{consistent_log init_map l}):
  Lemma (ensures (length (to_logk init_map l) = length l))
  = ()

let lemma_all_entries_valid (#vcfg:_) (init_map: slot_state_map vcfg) (l:logS vcfg{consistent_log init_map l}) (i:seq_index l):
  Lemma (ensures (let l' = prefix l i in
                  lemma_consistent_log_prefix_consistent init_map l i;
                  let ssm' = to_slot_state_map init_map l' in
                  valid_logS_entry ssm' (index l i)))
  = consistent_log_all_entries_valid init_map l i

let lemma_to_logk_index (#vcfg:_) (init_map: slot_state_map vcfg) (l:logS _{consistent_log init_map l}) (i:seq_index l):
  Lemma (ensures (let lk = to_logk init_map l in
                  let l' = prefix l i in
                  lemma_consistent_log_prefix_consistent init_map l i;
                  let ssm' = to_slot_state_map init_map l' in
                  lemma_all_entries_valid init_map l i;
                  index lk i = to_logk_entry ssm' (index l i)))
  = ()
