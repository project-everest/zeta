module Veritas.Intermediate.Logs

let lemma_consistent_log_prefix_consistent (#vcfg:_) (init_map: slot_state_map vcfg) (l:logS vcfg) (i:nat{i <= length l}):
  Lemma (requires (consistent_log init_map l))
        (ensures (consistent_log init_map (prefix l i))) = admit()

let to_logk (#vcfg:_) (init_map: slot_state_map vcfg) (l:logS vcfg{consistent_log init_map l}): logK = 
  admit()

let lemma_to_logk_length (#vcfg:_) (init_map: slot_state_map vcfg) (l:logS vcfg{consistent_log init_map l}):
  Lemma (ensures (length (to_logk init_map l) = length l))
  = admit()

let lemma_all_entries_valid (#vcfg:_) (init_map: slot_state_map vcfg) (l:logS vcfg{consistent_log init_map l}) (i:seq_index l):
  Lemma (ensures (let l' = prefix l i in
                  lemma_consistent_log_prefix_consistent init_map l i;
                  let ssm' = to_slot_state_map init_map l' in
                  valid_logS_entry ssm' (index l i)))
  = admit()

let lemma_to_logk_index (#vcfg:_) (init_map: slot_state_map vcfg) (l:logS _{consistent_log init_map l}) (i:seq_index l):
  Lemma (ensures (let lk = to_logk init_map l in
                  let l' = prefix l i in
                  lemma_consistent_log_prefix_consistent init_map l i;
                  let ssm' = to_slot_state_map init_map l' in
                  lemma_all_entries_valid init_map l i;
                  index lk i = to_logK_entry ssm' (index l i)))                  
  = admit()

(*


(* Reproducing definitions from Veritas.Verifier.Global *)

(* Reproducing definitions from Veritas.Verifier.TSLog *)






let lemma_logS_interleave_implies_state_ops_interleave #vcfg (l: logS vcfg) (gl: g_logS vcfg{interleave #(logS_entry vcfg) l gl})
  : Lemma (interleave #state_op (to_state_op_logS l) (to_state_op_glogS gl)) 
  = FStar.Squash.bind_squash
      #(interleave l gl)
      #(interleave (to_state_op_logS l) (to_state_op_glogS gl))
      ()
      (fun i -> 
        let i' = filter_map_interleaving is_state_op to_state_op i in
        FStar.Squash.return_squash i')
*)
